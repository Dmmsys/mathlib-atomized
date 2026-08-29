/-
Copyright (c) 2023 Yaël Dillies, Vladimir Ivanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Vladimir Ivanov
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Finset.Sups
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

/-!
# The Ahlswede-Zhang identity

This file proves the Ahlswede-Zhang identity, which is a nontrivial relation between the size of the
"truncated unions" of a set family. It sharpens the Lubell-Yamamoto-Meshalkin inequality
`Finset.lubell_yamamoto_meshalkin_inequality_sum_card_div_choose`, by making explicit the correction
term.

For a set family `𝒜` over a ground set of size `n`, the Ahlswede-Zhang identity states that the sum
of `|⋂ B ∈ 𝒜, B ⊆ A, B|/(|A| * n.choose |A|)` over all sets `A` is exactly `1`. This implies the LYM
inequality since for an antichain `𝒜` and every `A ∈ 𝒜` we have
`|⋂ B ∈ 𝒜, B ⊆ A, B|/(|A| * n.choose |A|) = 1 / n.choose |A|`.

## Main declarations

* `Finset.truncatedSup`: `s.truncatedSup a` is the supremum of all `b ≥ a` in `𝒜` if there are
  some, or `⊤` if there are none.
* `Finset.truncatedInf`: `s.truncatedInf a` is the infimum of all `b ≤ a` in `𝒜` if there are
  some, or `⊥` if there are none.
* `AhlswedeZhang.infSum`: LHS of the Ahlswede-Zhang identity.
* `AhlswedeZhang.le_infSum`: The sum of `1 / n.choose |A|` over an antichain is less than the RHS of
  the Ahlswede-Zhang identity.
* `AhlswedeZhang.infSum_eq_one`: Ahlswede-Zhang identity.

## References

* [R. Ahlswede, Z. Zhang, *An identity in combinatorial extremal theory*](https://doi.org/10.1016/0001-8708(90)90023-G)
* [D. T. Tru, *An AZ-style identity and Bollobás deficiency*](https://doi.org/10.1016/j.jcta.2007.03.005)
-/

@[expose] public section

section
variable (α : Type*) [Fintype α] [Nonempty α] {m n : Nat}

open Finset Fintype Nat

/--
lemma `binomial_sum_eq` / 引理 `binomial_sum_eq`

English:
lemma binomial_sum_eq
  given: (h : n < m)
  proof: by
  set f : Nat -> Rat := fun i => n.choose i * (m.choose i : Rat)⁻¹ with hf
  suffices forall i in range (n + 1), f i - f (i + 1) = n.choose i * (m - n) / ((m - i) * m.choose i) by
    rw [← sum_congr rfl this]; rw [sum_range_sub']; rw [hf]
    simp [choose_zero_right]
  intro i h₁
  rw [mem_range

中文:
引理 binomial_sum_eq
  条件: (h : n < m)
  证明: by
  set f : Nat -> Rat := fun i => n.choose i * (m.choose i : Rat)⁻¹ with hf
  suffices forall i in range (n + 1), f i - f (i + 1) = n.choose i * (m - n) / ((m - i) * m.choose i) by
    rw [← sum_congr rfl this]; rw [sum_range_sub']; rw [hf]
    simp [choose_zero_right]
  intro i h₁
  rw [mem_range
-/
private lemma binomial_sum_eq (h : n < m) :
    ∑ i in range (n + 1), (n.choose i * (m - n) / ((m - i) * m.choose i) : Rat) = 1 := by
  set f : Nat -> Rat := fun i => n.choose i * (m.choose i : Rat)⁻¹ with hf
  suffices forall i in range (n + 1), f i - f (i + 1) = n.choose i * (m - n) / ((m - i) * m.choose i) by
    rw [← sum_congr rfl this]; rw [sum_range_sub']; rw [hf]
    simp [choose_zero_right]
  intro i h₁
  rw [mem_range] at h₁
  have h₁ := le_of_lt_succ h₁
  have h₂ := h₁.trans_lt h
  have h₃ := h₂.le
  have hi₄ : (i + 1 : Rat) != 0 := i.cast_add_one_ne_zero
  have := congr_arg ((↑) : Nat -> Rat) (choose_succ_right_eq m i)
  push_cast at this
  dsimp [f, hf]
  rw [(eq_mul_inv_iff_mul_eq₀ hi₄).mpr this]
  have := congr_arg ((↑) : Nat -> Rat) (choose_succ_right_eq n i)
  push_cast at this
  rw [(eq_mul_inv_iff_mul_eq₀ hi₄).mpr this]
  have : (m - i : Rat) != 0 := sub_ne_zero_of_ne (cast_lt.mpr h₂).ne'
  have : (m.choose i : Rat) != 0 := cast_ne_zero.2 (choose_pos h₂.le).ne'
  simp [field, *]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Fintype.sum_div_mul_card_choose_card` / 引理 `Fintype.sum_div_mul_card_choose_card`

English:
lemma Fintype.sum_div_mul_card_choose_card
  proof: by
  rw [← powerset_univ]; rw [powerset_card_disjiUnion]; rw [sum_disjiUnion]
  have : forall {x : Nat}, forall s in powersetCard x (univ : Finset α),
    (card α / ((card α - #s) * (card α).choose #s) : Rat) =
      card α / ((card α - x) * (card α).choose x) := by
    intro n s hs
    rw [mem_powe

中文:
引理 Fintype.sum_div_mul_card_choose_card
  证明: by
  rw [← powerset_univ]; rw [powerset_card_disjiUnion]; rw [sum_disjiUnion]
  have : forall {x : Nat}, forall s in powersetCard x (univ : Finset α),
    (card α / ((card α - #s) * (card α).choose #s) : Rat) =
      card α / ((card α - x) * (card α).choose x) := by
    intro n s hs
    rw [mem_powe
-/
private lemma Fintype.sum_div_mul_card_choose_card :
    ∑ s : Finset α, (card α / ((card α - #s) * (card α).choose #s) : Rat) =
      card α * ∑ k in range (card α), (↑k)⁻¹ + 1 := by
  rw [← powerset_univ]; rw [powerset_card_disjiUnion]; rw [sum_disjiUnion]
  have : forall {x : Nat}, forall s in powersetCard x (univ : Finset α),
    (card α / ((card α - #s) * (card α).choose #s) : Rat) =
      card α / ((card α - x) * (card α).choose x) := by
    intro n s hs
    rw [mem_powersetCard_univ.1 hs]
  simp_rw [Finset.sum_congr rfl this, sum_const, card_powersetCard, card_univ, nsmul_eq_mul,
    mul_div, mul_comm, ← mul_div]
  rw [← mul_sum]; rw [← mul_inv_cancel₀ (cast_ne_zero.mpr card_ne_zero : (card α : Rat) != 0)]; rw [← mul_add]; rw [add_comm _ ((card α)⁻¹ : Rat)]; rw [← sum_insert (f := fun x : Nat => (x⁻¹ : Rat)) notMem_range_self]; rw [← range_add_one]
  have (n) (hn : n in range (card α + 1)) :
      ((card α).choose n / ((card α - n) * (card α).choose n) : Rat) = (card α - n : Rat)⁻¹ := by
    rw [div_mul_cancel_right₀]
    exact cast_ne_zero.2 (choose_pos <| mem_range_succ_iff.1 hn).ne'
  simp only [Finset.sum_congr rfl this, mul_eq_mul_left_iff, cast_eq_zero]
convert! Or.inl sum_range_reflect _ _ with a ha
  rw [add_tsub_cancel_right]; rw [cast_sub (mem_range_succ_iff.mp ha)]

end

open scoped FinsetFamily

namespace Finset
variable {α β : Type*}

/-! ### Truncated supremum, truncated infimum -/

section SemilatticeSup
variable [SemilatticeSup α] [SemilatticeSup β] [BoundedOrder β] {s t : Finset α} {a : α}

set_option backward.privateInPublic true in
/--
lemma `sup_aux` / 引理 `sup_aux`

English:
lemma sup_aux
  given: [DecidableLE α]
  statement: a in lowerClosure s -> {b in s | a <= b}.Nonempty
  proof: fun ⟨b, hb, hab⟩ => ⟨b, mem_filter.2 ⟨hb, hab⟩⟩

中文:
引理 sup_aux
  条件: [DecidableLE α]
  结论: a in lowerClosure s -> {b in s | a <= b}.Nonempty
  证明: fun ⟨b, hb, hab⟩ => ⟨b, mem_filter.2 ⟨hb, hab⟩⟩
-/
private lemma sup_aux [DecidableLE α] : a in lowerClosure s -> {b in s | a <= b}.Nonempty :=
  fun ⟨b, hb, hab⟩ => ⟨b, mem_filter.2 ⟨hb, hab⟩⟩

/--
lemma `lower_aux` / 引理 `lower_aux`

English:
lemma lower_aux
  given: [DecidableEq α]
  proof: by
  rw [coe_union]; rw [lowerClosure_union]; rw [LowerSet.mem_sup_iff]

中文:
引理 lower_aux
  条件: [DecidableEq α]
  证明: by
  rw [coe_union]; rw [lowerClosure_union]; rw [LowerSet.mem_sup_iff]
-/
private lemma lower_aux [DecidableEq α] :
    a in lowerClosure ↑(s union t) ↔ a in lowerClosure s ∨ a in lowerClosure t := by
  rw [coe_union]; rw [lowerClosure_union]; rw [LowerSet.mem_sup_iff]

variable [DecidableLE α] [OrderTop α]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `truncatedSup` / `truncatedSup` 的定义

English:
definition truncatedSup
  signature: (s : Finset α) (a : α)
  body: if h : a in lowerClosure s then {b in s | a <= b}.sup' (sup_aux h) id else ⊤

中文:
定义 truncatedSup
  签名: (s : Finset α) (a : α)
  定义体: if h : a in lowerClosure s then {b in s | a <= b}.sup' (sup_aux h) id else ⊤

Depends on / 依赖: lowerClosure, sup_aux
-/
def truncatedSup (s : Finset α) (a : α) : α :=
  if h : a in lowerClosure s then {b in s | a <= b}.sup' (sup_aux h) id else ⊤

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
lemma `truncatedSup_of_mem` / 引理 `truncatedSup_of_mem`

English:
lemma truncatedSup_of_mem
  given: (h : a in lowerClosure s)
  proof: dif_pos h

中文:
引理 truncatedSup_of_mem
  条件: (h : a in lowerClosure s)
  证明: dif_pos h

Depends on / 依赖: dif_pos
-/
lemma truncatedSup_of_mem (h : a in lowerClosure s) :
    truncatedSup s a = {b in s | a <= b}.sup' (sup_aux h) id := dif_pos h

/--
lemma `truncatedSup_of_notMem` / 引理 `truncatedSup_of_notMem`

English:
lemma truncatedSup_of_notMem
  given: (h : a ∉ lowerClosure s)
  statement: truncatedSup s a = ⊤
  proof: dif_neg h

中文:
引理 truncatedSup_of_notMem
  条件: (h : a ∉ lowerClosure s)
  结论: truncatedSup s a = ⊤
  证明: dif_neg h

Depends on / 依赖: dif_neg
-/
lemma truncatedSup_of_notMem (h : a ∉ lowerClosure s) : truncatedSup s a = ⊤ := dif_neg h

/--
lemma `truncatedSup_empty` / 引理 `truncatedSup_empty`

English:
lemma truncatedSup_empty
  given: (a : α)
  statement: truncatedSup ∅ a = ⊤
  proof: truncatedSup_of_notMem (by simp)

中文:
引理 truncatedSup_empty
  条件: (a : α)
  结论: truncatedSup ∅ a = ⊤
  证明: truncatedSup_of_notMem (by simp)
-/
@[simp] lemma truncatedSup_empty (a : α) : truncatedSup ∅ a = ⊤ := truncatedSup_of_notMem (by simp)

/--
lemma `truncatedSup_singleton` / 引理 `truncatedSup_singleton`

English:
lemma truncatedSup_singleton
  given: (b a : α)
  statement: truncatedSup {b} a = if a <= b then b else ⊤
  proof: by
  simp [truncatedSup]; split_ifs <;> simp [Finset.filter_true_of_mem, *]

中文:
引理 truncatedSup_singleton
  条件: (b a : α)
  结论: truncatedSup {b} a = if a <= b then b else ⊤
  证明: by
  simp [truncatedSup]; split_ifs <;> simp [Finset.filter_true_of_mem, *]
-/
@[simp] lemma truncatedSup_singleton (b a : α) : truncatedSup {b} a = if a <= b then b else ⊤ := by
  simp [truncatedSup]; split_ifs <;> simp [Finset.filter_true_of_mem, *]

/--
lemma `le_truncatedSup` / 引理 `le_truncatedSup`

English:
lemma le_truncatedSup
  statement: a <= truncatedSup s a
  proof: by
  rw [truncatedSup]
  split_ifs with h
  · obtain ⟨ℬ, hb, h⟩ := h
exact h.trans le_sup' id mem_filter.2 ⟨hb, h⟩
  · exact le_top

中文:
引理 le_truncatedSup
  结论: a <= truncatedSup s a
  证明: by
  rw [truncatedSup]
  split_ifs with h
  · obtain ⟨ℬ, hb, h⟩ := h
exact h.trans le_sup' id mem_filter.2 ⟨hb, h⟩
  · exact le_top

Depends on / 依赖: h.trans, le_sup, le_top, mem_filter, split_ifs, truncatedSup
-/
lemma le_truncatedSup : a <= truncatedSup s a := by
  rw [truncatedSup]
  split_ifs with h
  · obtain ⟨ℬ, hb, h⟩ := h
exact h.trans le_sup' id mem_filter.2 ⟨hb, h⟩
  · exact le_top

/--
lemma `map_truncatedSup` / 引理 `map_truncatedSup`

English:
lemma map_truncatedSup
  given: [DecidableLE β] (e : α ≃o β) (s : Finset α) (a : α)
  proof: by
  have : e a in lowerClosure (s.map e.toEquiv.toEmbedding : Set β) ↔ a in lowerClosure s := by simp
  simp_rw [truncatedSup, apply_dite e, map_finset_sup', map_top, this]
  congr with h
  simp only [filter_map, Function.comp_def, Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv,
    OrderIso.le_iff_l

中文:
引理 map_truncatedSup
  条件: [DecidableLE β] (e : α ≃o β) (s : Finset α) (a : α)
  证明: by
  have : e a in lowerClosure (s.map e.toEquiv.toEmbedding : Set β) ↔ a in lowerClosure s := by simp
  simp_rw [truncatedSup, apply_dite e, map_finset_sup', map_top, this]
  congr with h
  simp only [filter_map, Function.comp_def, Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv,
    OrderIso.le_iff_l

Depends on / 依赖: Equiv.coe_toEmbedding, Function, Function.comp_def, OrderIso, OrderIso.le_iff_le, RelIso, RelIso.coe_fn_toEquiv, _map, apply_dite, coe_fn_toEquiv, coe_toEmbedding, comp_def, e.toEquiv.toEmbedding, filter_map, le_iff_le, lowerClosure, map_finset_sup, map_top, s.map, simp_rw
-/
lemma map_truncatedSup [DecidableLE β] (e : α ≃o β) (s : Finset α) (a : α) :
    e (truncatedSup s a) = truncatedSup (s.map e.toEquiv.toEmbedding) (e a) := by
  have : e a in lowerClosure (s.map e.toEquiv.toEmbedding : Set β) ↔ a in lowerClosure s := by simp
  simp_rw [truncatedSup, apply_dite e, map_finset_sup', map_top, this]
  congr with h
  simp only [filter_map, Function.comp_def, Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv,
    OrderIso.le_iff_le, id, sup'_map]

/--
lemma `truncatedSup_of_isAntichain` / 引理 `truncatedSup_of_isAntichain`

English:
lemma truncatedSup_of_isAntichain
  given: (hs : IsAntichain (· <= ·) (s : Set α)) (ha : a in s)
  proof: by
  refine le_antisymm ?_ le_truncatedSup
  simp_rw [truncatedSup_of_mem (subset_lowerClosure ha), sup'_le_iff, mem_filter]
  rintro b ⟨hb, hab⟩
  exact (hs.eq ha hb hab).ge

中文:
引理 truncatedSup_of_isAntichain
  条件: (hs : IsAntichain (· <= ·) (s : Set α)) (ha : a in s)
  证明: by
  refine le_antisymm ?_ le_truncatedSup
  simp_rw [truncatedSup_of_mem (subset_lowerClosure ha), sup'_le_iff, mem_filter]
  rintro b ⟨hb, hab⟩
  exact (hs.eq ha hb hab).ge

Depends on / 依赖: _le_iff, hs.eq, le_antisymm, le_truncatedSup, mem_filter, simp_rw, subset_lowerClosure, truncatedSup_of_mem
-/
lemma truncatedSup_of_isAntichain (hs : IsAntichain (· <= ·) (s : Set α)) (ha : a in s) :
    truncatedSup s a = a := by
  refine le_antisymm ?_ le_truncatedSup
  simp_rw [truncatedSup_of_mem (subset_lowerClosure ha), sup'_le_iff, mem_filter]
  rintro b ⟨hb, hab⟩
  exact (hs.eq ha hb hab).ge

variable [DecidableEq α]

/--
lemma `truncatedSup_union` / 引理 `truncatedSup_union`

English:
lemma truncatedSup_union
  given: (hs : a in lowerClosure s) (ht : a in lowerClosure t)
  proof: by
  simpa only [truncatedSup_of_mem, hs, ht, lower_aux.2 (Or.inl hs), filter_union] using
    sup'_union _ _ _

中文:
引理 truncatedSup_union
  条件: (hs : a in lowerClosure s) (ht : a in lowerClosure t)
  证明: by
  simpa only [truncatedSup_of_mem, hs, ht, lower_aux.2 (Or.inl hs), filter_union] using
    sup'_union _ _ _

Depends on / 依赖: Or.inl, _union, filter_union, lower_aux, truncatedSup_of_mem
-/
lemma truncatedSup_union (hs : a in lowerClosure s) (ht : a in lowerClosure t) :
    truncatedSup (s union t) a = truncatedSup s a ⊔ truncatedSup t a := by
  simpa only [truncatedSup_of_mem, hs, ht, lower_aux.2 (Or.inl hs), filter_union] using
    sup'_union _ _ _

/--
lemma `truncatedSup_union_left` / 引理 `truncatedSup_union_left`

English:
lemma truncatedSup_union_left
  given: (hs : a in lowerClosure s) (ht : a ∉ lowerClosure t)
  proof: by
  simp only [mem_lowerClosure, mem_coe, not_exists, not_and] at ht
  simp only [truncatedSup_of_mem, hs, filter_union, filter_false_of_mem ht, union_empty,
    lower_aux.2 (Or.inl hs)]

中文:
引理 truncatedSup_union_left
  条件: (hs : a in lowerClosure s) (ht : a ∉ lowerClosure t)
  证明: by
  simp only [mem_lowerClosure, mem_coe, not_exists, not_and] at ht
  simp only [truncatedSup_of_mem, hs, filter_union, filter_false_of_mem ht, union_empty,
    lower_aux.2 (Or.inl hs)]

Depends on / 依赖: Or.inl, filter_false_of_mem, filter_union, lower_aux, mem_coe, mem_lowerClosure, not_and, not_exists, truncatedSup_of_mem, union_empty
-/
lemma truncatedSup_union_left (hs : a in lowerClosure s) (ht : a ∉ lowerClosure t) :
    truncatedSup (s union t) a = truncatedSup s a := by
  simp only [mem_lowerClosure, mem_coe, not_exists, not_and] at ht
  simp only [truncatedSup_of_mem, hs, filter_union, filter_false_of_mem ht, union_empty,
    lower_aux.2 (Or.inl hs)]

/--
lemma `truncatedSup_union_right` / 引理 `truncatedSup_union_right`

English:
lemma truncatedSup_union_right
  given: (hs : a ∉ lowerClosure s) (ht : a in lowerClosure t)
  proof: by rw [union_comm, truncatedSup_union_left ht hs]

中文:
引理 truncatedSup_union_right
  条件: (hs : a ∉ lowerClosure s) (ht : a in lowerClosure t)
  证明: by rw [union_comm, truncatedSup_union_left ht hs]

Depends on / 依赖: truncatedSup_union_left, union_comm
-/
lemma truncatedSup_union_right (hs : a ∉ lowerClosure s) (ht : a in lowerClosure t) :
    truncatedSup (s union t) a = truncatedSup t a := by rw [union_comm, truncatedSup_union_left ht hs]

/--
lemma `truncatedSup_union_of_notMem` / 引理 `truncatedSup_union_of_notMem`

English:
lemma truncatedSup_union_of_notMem
  given: (hs : a ∉ lowerClosure s) (ht : a ∉ lowerClosure t)
  proof: truncatedSup_of_notMem fun h => (lower_aux.1 h).elim hs ht

中文:
引理 truncatedSup_union_of_notMem
  条件: (hs : a ∉ lowerClosure s) (ht : a ∉ lowerClosure t)
  证明: truncatedSup_of_notMem fun h => (lower_aux.1 h).elim hs ht

Depends on / 依赖: lower_aux, truncatedSup_of_notMem
-/
lemma truncatedSup_union_of_notMem (hs : a ∉ lowerClosure s) (ht : a ∉ lowerClosure t) :
    truncatedSup (s union t) a = ⊤ := truncatedSup_of_notMem fun h => (lower_aux.1 h).elim hs ht

end SemilatticeSup

section SemilatticeInf
variable [SemilatticeInf α] [SemilatticeInf β]
  [BoundedOrder β] [DecidableLE β] {s t : Finset α} {a : α}

set_option backward.privateInPublic true in
/--
lemma `inf_aux` / 引理 `inf_aux`

English:
lemma inf_aux
  given: [DecidableLE α]
  statement: a in upperClosure s -> {b in s | b <= a}.Nonempty
  proof: fun ⟨b, hb, hab⟩ => ⟨b, mem_filter.2 ⟨hb, hab⟩⟩

中文:
引理 inf_aux
  条件: [DecidableLE α]
  结论: a in upperClosure s -> {b in s | b <= a}.Nonempty
  证明: fun ⟨b, hb, hab⟩ => ⟨b, mem_filter.2 ⟨hb, hab⟩⟩
-/
private lemma inf_aux [DecidableLE α] : a in upperClosure s -> {b in s | b <= a}.Nonempty :=
  fun ⟨b, hb, hab⟩ => ⟨b, mem_filter.2 ⟨hb, hab⟩⟩

/--
lemma `upper_aux` / 引理 `upper_aux`

English:
lemma upper_aux
  given: [DecidableEq α]
  proof: by
  rw [coe_union]; rw [upperClosure_union]; rw [UpperSet.mem_inf_iff]

中文:
引理 upper_aux
  条件: [DecidableEq α]
  证明: by
  rw [coe_union]; rw [upperClosure_union]; rw [UpperSet.mem_inf_iff]
-/
private lemma upper_aux [DecidableEq α] :
    a in upperClosure ↑(s union t) ↔ a in upperClosure s ∨ a in upperClosure t := by
  rw [coe_union]; rw [upperClosure_union]; rw [UpperSet.mem_inf_iff]

variable [DecidableLE α] [BoundedOrder α]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `truncatedInf` / `truncatedInf` 的定义

English:
definition truncatedInf
  signature: (s : Finset α) (a : α)
  body: if h : a in upperClosure s then {b in s | b <= a}.inf' (inf_aux h) id else ⊥

中文:
定义 truncatedInf
  签名: (s : Finset α) (a : α)
  定义体: if h : a in upperClosure s then {b in s | b <= a}.inf' (inf_aux h) id else ⊥

Depends on / 依赖: inf_aux, upperClosure
-/
def truncatedInf (s : Finset α) (a : α) : α :=
  if h : a in upperClosure s then {b in s | b <= a}.inf' (inf_aux h) id else ⊥

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
lemma `truncatedInf_of_mem` / 引理 `truncatedInf_of_mem`

English:
lemma truncatedInf_of_mem
  given: (h : a in upperClosure s)
  proof: dif_pos h

中文:
引理 truncatedInf_of_mem
  条件: (h : a in upperClosure s)
  证明: dif_pos h

Depends on / 依赖: dif_pos
-/
lemma truncatedInf_of_mem (h : a in upperClosure s) :
    truncatedInf s a = {b in s | b <= a}.inf' (inf_aux h) id := dif_pos h

/--
lemma `truncatedInf_of_notMem` / 引理 `truncatedInf_of_notMem`

English:
lemma truncatedInf_of_notMem
  given: (h : a ∉ upperClosure s)
  statement: truncatedInf s a = ⊥
  proof: dif_neg h

中文:
引理 truncatedInf_of_notMem
  条件: (h : a ∉ upperClosure s)
  结论: truncatedInf s a = ⊥
  证明: dif_neg h

Depends on / 依赖: add_le_add_left, dif_neg
-/
lemma truncatedInf_of_notMem (h : a ∉ upperClosure s) : truncatedInf s a = ⊥ := dif_neg h

/--
lemma `truncatedInf_le` / 引理 `truncatedInf_le`

English:
lemma truncatedInf_le
  statement: truncatedInf s a <= a
  proof: by
  unfold truncatedInf
  split_ifs with h
  · obtain ⟨b, hb, hba⟩ := h
exact hba.trans' inf'_le id mem_filter.2 ⟨hb, ‹_›⟩
  · exact bot_le

中文:
引理 truncatedInf_le
  结论: truncatedInf s a <= a
  证明: by
  unfold truncatedInf
  split_ifs with h
  · obtain ⟨b, hb, hba⟩ := h
exact hba.trans' inf'_le id mem_filter.2 ⟨hb, ‹_›⟩
  · exact bot_le

Depends on / 依赖: bot_le, hba.trans, le_of_add_le_add_left, mem_filter, split_ifs, truncatedInf
-/
lemma truncatedInf_le : truncatedInf s a <= a := by
  unfold truncatedInf
  split_ifs with h
  · obtain ⟨b, hb, hba⟩ := h
exact hba.trans' inf'_le id mem_filter.2 ⟨hb, ‹_›⟩
  · exact bot_le

/--
lemma `truncatedInf_empty` / 引理 `truncatedInf_empty`

English:
lemma truncatedInf_empty
  given: (a : α)
  statement: truncatedInf ∅ a = ⊥
  proof: truncatedInf_of_notMem (by simp)

中文:
引理 truncatedInf_empty
  条件: (a : α)
  结论: truncatedInf ∅ a = ⊥
  证明: truncatedInf_of_notMem (by simp)
-/
@[simp] lemma truncatedInf_empty (a : α) : truncatedInf ∅ a = ⊥ := truncatedInf_of_notMem (by simp)

/--
lemma `truncatedInf_singleton` / 引理 `truncatedInf_singleton`

English:
lemma truncatedInf_singleton
  given: (b a : α)
  statement: truncatedInf {b} a = if b <= a then b else ⊥
  proof: by
  simp only [truncatedInf, coe_singleton, upperClosure_singleton, UpperSet.mem_Ici_iff,
    id_eq]
  split_ifs <;> simp [Finset.filter_true_of_mem, *]

中文:
引理 truncatedInf_singleton
  条件: (b a : α)
  结论: truncatedInf {b} a = if b <= a then b else ⊥
  证明: by
  simp only [truncatedInf, coe_singleton, upperClosure_singleton, UpperSet.mem_Ici_iff,
    id_eq]
  split_ifs <;> simp [Finset.filter_true_of_mem, *]
-/
@[simp] lemma truncatedInf_singleton (b a : α) : truncatedInf {b} a = if b <= a then b else ⊥ := by
  simp only [truncatedInf, coe_singleton, upperClosure_singleton, UpperSet.mem_Ici_iff,
    id_eq]
  split_ifs <;> simp [Finset.filter_true_of_mem, *]

/--
lemma `map_truncatedInf` / 引理 `map_truncatedInf`

English:
lemma map_truncatedInf
  given: (e : α ≃o β) (s : Finset α) (a : α)
  proof: by
  have : e a in upperClosure (s.map e.toEquiv.toEmbedding) ↔ a in upperClosure s := by simp
  simp_rw [truncatedInf, apply_dite e, map_finset_inf', map_bot, this]
  congr with h
  simp only [filter_map, Function.comp_def, Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv,
    OrderIso.le_iff_le, id, i

中文:
引理 map_truncatedInf
  条件: (e : α ≃o β) (s : Finset α) (a : α)
  证明: by
  have : e a in upperClosure (s.map e.toEquiv.toEmbedding) ↔ a in upperClosure s := by simp
  simp_rw [truncatedInf, apply_dite e, map_finset_inf', map_bot, this]
  congr with h
  simp only [filter_map, Function.comp_def, Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv,
    OrderIso.le_iff_le, id, i

Depends on / 依赖: Equiv.coe_toEmbedding, Function, Function.comp_def, OrderIso, OrderIso.le_iff_le, RelIso, RelIso.coe_fn_toEquiv, _map, apply_dite, coe_fn_toEquiv, coe_toEmbedding, comp_def, e.toEquiv.toEmbedding, filter_map, le_iff_le, map_bot, map_finset_inf, s.map, simp_rw, toEmbedding
-/
lemma map_truncatedInf (e : α ≃o β) (s : Finset α) (a : α) :
    e (truncatedInf s a) = truncatedInf (s.map e.toEquiv.toEmbedding) (e a) := by
  have : e a in upperClosure (s.map e.toEquiv.toEmbedding) ↔ a in upperClosure s := by simp
  simp_rw [truncatedInf, apply_dite e, map_finset_inf', map_bot, this]
  congr with h
  simp only [filter_map, Function.comp_def, Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv,
    OrderIso.le_iff_le, id, inf'_map]

/--
lemma `truncatedInf_of_isAntichain` / 引理 `truncatedInf_of_isAntichain`

English:
lemma truncatedInf_of_isAntichain
  given: (hs : IsAntichain (· <= ·) (s : Set α)) (ha : a in s)
  proof: by
  refine le_antisymm truncatedInf_le ?_
  simp_rw [truncatedInf_of_mem (subset_upperClosure ha), le_inf'_iff, mem_filter]
  rintro b ⟨hb, hba⟩
  exact (hs.eq hb ha hba).ge

中文:
引理 truncatedInf_of_isAntichain
  条件: (hs : IsAntichain (· <= ·) (s : Set α)) (ha : a in s)
  证明: by
  refine le_antisymm truncatedInf_le ?_
  simp_rw [truncatedInf_of_mem (subset_upperClosure ha), le_inf'_iff, mem_filter]
  rintro b ⟨hb, hba⟩
  exact (hs.eq hb ha hba).ge

Depends on / 依赖: _iff, hs.eq, le_antisymm, le_inf, mem_filter, simp_rw, subset_upperClosure, truncatedInf_le, truncatedInf_of_mem
-/
lemma truncatedInf_of_isAntichain (hs : IsAntichain (· <= ·) (s : Set α)) (ha : a in s) :
    truncatedInf s a = a := by
  refine le_antisymm truncatedInf_le ?_
  simp_rw [truncatedInf_of_mem (subset_upperClosure ha), le_inf'_iff, mem_filter]
  rintro b ⟨hb, hba⟩
  exact (hs.eq hb ha hba).ge

variable [DecidableEq α]

/--
lemma `truncatedInf_union` / 引理 `truncatedInf_union`

English:
lemma truncatedInf_union
  given: (hs : a in upperClosure s) (ht : a in upperClosure t)
  proof: by
  simpa only [truncatedInf_of_mem, hs, ht, upper_aux.2 (Or.inl hs), filter_union] using
    inf'_union _ _ _

中文:
引理 truncatedInf_union
  条件: (hs : a in upperClosure s) (ht : a in upperClosure t)
  证明: by
  simpa only [truncatedInf_of_mem, hs, ht, upper_aux.2 (Or.inl hs), filter_union] using
    inf'_union _ _ _

Depends on / 依赖: Or.inl, _union, filter_union, truncatedInf_of_mem, upper_aux
-/
lemma truncatedInf_union (hs : a in upperClosure s) (ht : a in upperClosure t) :
    truncatedInf (s union t) a = truncatedInf s a ⊓ truncatedInf t a := by
  simpa only [truncatedInf_of_mem, hs, ht, upper_aux.2 (Or.inl hs), filter_union] using
    inf'_union _ _ _

/--
lemma `truncatedInf_union_left` / 引理 `truncatedInf_union_left`

English:
lemma truncatedInf_union_left
  given: (hs : a in upperClosure s) (ht : a ∉ upperClosure t)
  proof: by
  simp only [mem_upperClosure, mem_coe, not_exists, not_and] at ht
  simp only [truncatedInf_of_mem, hs, filter_union, filter_false_of_mem ht, union_empty,
    upper_aux.2 (Or.inl hs)]

中文:
引理 truncatedInf_union_left
  条件: (hs : a in upperClosure s) (ht : a ∉ upperClosure t)
  证明: by
  simp only [mem_upperClosure, mem_coe, not_exists, not_and] at ht
  simp only [truncatedInf_of_mem, hs, filter_union, filter_false_of_mem ht, union_empty,
    upper_aux.2 (Or.inl hs)]

Depends on / 依赖: Or.inl, filter_false_of_mem, filter_union, mem_coe, mem_upperClosure, not_and, not_exists, truncatedInf_of_mem, union_empty, upper_aux
-/
lemma truncatedInf_union_left (hs : a in upperClosure s) (ht : a ∉ upperClosure t) :
    truncatedInf (s union t) a = truncatedInf s a := by
  simp only [mem_upperClosure, mem_coe, not_exists, not_and] at ht
  simp only [truncatedInf_of_mem, hs, filter_union, filter_false_of_mem ht, union_empty,
    upper_aux.2 (Or.inl hs)]

/--
lemma `truncatedInf_union_right` / 引理 `truncatedInf_union_right`

English:
lemma truncatedInf_union_right
  given: (hs : a ∉ upperClosure s) (ht : a in upperClosure t)
  proof: by
  rw [union_comm]; rw [truncatedInf_union_left ht hs]

中文:
引理 truncatedInf_union_right
  条件: (hs : a ∉ upperClosure s) (ht : a in upperClosure t)
  证明: by
  rw [union_comm]; rw [truncatedInf_union_left ht hs]

Depends on / 依赖: truncatedInf_union_left, union_comm
-/
lemma truncatedInf_union_right (hs : a ∉ upperClosure s) (ht : a in upperClosure t) :
    truncatedInf (s union t) a = truncatedInf t a := by
  rw [union_comm]; rw [truncatedInf_union_left ht hs]

/--
lemma `truncatedInf_union_of_notMem` / 引理 `truncatedInf_union_of_notMem`

English:
lemma truncatedInf_union_of_notMem
  given: (hs : a ∉ upperClosure s) (ht : a ∉ upperClosure t)
  proof: truncatedInf_of_notMem by rw [coe_union, upperClosure_union]; exact fun h => h.elim hs ht

中文:
引理 truncatedInf_union_of_notMem
  条件: (hs : a ∉ upperClosure s) (ht : a ∉ upperClosure t)
  证明: truncatedInf_of_notMem by rw [coe_union, upperClosure_union]; exact fun h => h.elim hs ht

Depends on / 依赖: coe_union, h.elim, truncatedInf_of_notMem, upperClosure_union
-/
lemma truncatedInf_union_of_notMem (hs : a ∉ upperClosure s) (ht : a ∉ upperClosure t) :
    truncatedInf (s union t) a = ⊥ :=
truncatedInf_of_notMem by rw [coe_union, upperClosure_union]; exact fun h => h.elim hs ht

end SemilatticeInf

section DistribLattice
variable [DistribLattice α] [DecidableEq α] {s t : Finset α} {a : α}

/--
lemma `infs_aux` / 引理 `infs_aux`

English:
lemma infs_aux
  statement: a in lowerClosure ↑(s ⊼ t) ↔ a in lowerClosure s ∧ a in lowerClosure t
  proof: by
  rw [coe_infs]; rw [lowerClosure_infs]; rw [LowerSet.mem_inf_iff]

中文:
引理 infs_aux
  结论: a in lowerClosure ↑(s ⊼ t) ↔ a in lowerClosure s ∧ a in lowerClosure t
  证明: by
  rw [coe_infs]; rw [lowerClosure_infs]; rw [LowerSet.mem_inf_iff]
-/
private lemma infs_aux : a in lowerClosure ↑(s ⊼ t) ↔ a in lowerClosure s ∧ a in lowerClosure t := by
  rw [coe_infs]; rw [lowerClosure_infs]; rw [LowerSet.mem_inf_iff]

/--
lemma `sups_aux` / 引理 `sups_aux`

English:
lemma sups_aux
  statement: a in upperClosure ↑(s ⊻ t) ↔ a in upperClosure s ∧ a in upperClosure t
  proof: by
  rw [coe_sups]; rw [upperClosure_sups]; rw [UpperSet.mem_sup_iff]

中文:
引理 sups_aux
  结论: a in upperClosure ↑(s ⊻ t) ↔ a in upperClosure s ∧ a in upperClosure t
  证明: by
  rw [coe_sups]; rw [upperClosure_sups]; rw [UpperSet.mem_sup_iff]
-/
private lemma sups_aux : a in upperClosure ↑(s ⊻ t) ↔ a in upperClosure s ∧ a in upperClosure t := by
  rw [coe_sups]; rw [upperClosure_sups]; rw [UpperSet.mem_sup_iff]

variable [DecidableLE α] [BoundedOrder α]

/--
lemma `truncatedSup_infs` / 引理 `truncatedSup_infs`

English:
lemma truncatedSup_infs
  given: (hs : a in lowerClosure s) (ht : a in lowerClosure t)
  proof: by
  simp only [truncatedSup_of_mem, hs, ht, infs_aux.2 ⟨hs, ht⟩, sup'_inf_sup', filter_infs_le]
  simp_rw [← image_inf_product]
  rw [sup'_image]
  simp [Function.uncurry_def]

中文:
引理 truncatedSup_infs
  条件: (hs : a in lowerClosure s) (ht : a in lowerClosure t)
  证明: by
  simp only [truncatedSup_of_mem, hs, ht, infs_aux.2 ⟨hs, ht⟩, sup'_inf_sup', filter_infs_le]
  simp_rw [← image_inf_product]
  rw [sup'_image]
  simp [Function.uncurry_def]

Depends on / 依赖: Function, Function.uncurry_def, _image, _inf_sup, filter_infs_le, image_inf_product, infs_aux, simp_rw, truncatedSup_of_mem, uncurry_def
-/
lemma truncatedSup_infs (hs : a in lowerClosure s) (ht : a in lowerClosure t) :
    truncatedSup (s ⊼ t) a = truncatedSup s a ⊓ truncatedSup t a := by
  simp only [truncatedSup_of_mem, hs, ht, infs_aux.2 ⟨hs, ht⟩, sup'_inf_sup', filter_infs_le]
  simp_rw [← image_inf_product]
  rw [sup'_image]
  simp [Function.uncurry_def]

/--
lemma `truncatedInf_sups` / 引理 `truncatedInf_sups`

English:
lemma truncatedInf_sups
  given: (hs : a in upperClosure s) (ht : a in upperClosure t)
  proof: by
  simp only [truncatedInf_of_mem, hs, ht, sups_aux.2 ⟨hs, ht⟩, inf'_sup_inf', filter_sups_le]
  simp_rw [← image_sup_product]
  rw [inf'_image]
  simp [Function.uncurry_def]

中文:
引理 truncatedInf_sups
  条件: (hs : a in upperClosure s) (ht : a in upperClosure t)
  证明: by
  simp only [truncatedInf_of_mem, hs, ht, sups_aux.2 ⟨hs, ht⟩, inf'_sup_inf', filter_sups_le]
  simp_rw [← image_sup_product]
  rw [inf'_image]
  simp [Function.uncurry_def]

Depends on / 依赖: Function, Function.uncurry_def, _image, _sup_inf, filter_sups_le, image_sup_product, simp_rw, sups_aux, truncatedInf_of_mem, uncurry_def
-/
lemma truncatedInf_sups (hs : a in upperClosure s) (ht : a in upperClosure t) :
    truncatedInf (s ⊻ t) a = truncatedInf s a ⊔ truncatedInf t a := by
  simp only [truncatedInf_of_mem, hs, ht, sups_aux.2 ⟨hs, ht⟩, inf'_sup_inf', filter_sups_le]
  simp_rw [← image_sup_product]
  rw [inf'_image]
  simp [Function.uncurry_def]

/--
lemma `truncatedSup_infs_of_notMem` / 引理 `truncatedSup_infs_of_notMem`

English:
lemma truncatedSup_infs_of_notMem
  given: (ha : a ∉ lowerClosure s ⊓ lowerClosure t)
  proof: truncatedSup_of_notMem by rwa [coe_infs, lowerClosure_infs]

中文:
引理 truncatedSup_infs_of_notMem
  条件: (ha : a ∉ lowerClosure s ⊓ lowerClosure t)
  证明: truncatedSup_of_notMem by rwa [coe_infs, lowerClosure_infs]

Depends on / 依赖: coe_infs, lowerClosure_infs, truncatedSup_of_notMem
-/
lemma truncatedSup_infs_of_notMem (ha : a ∉ lowerClosure s ⊓ lowerClosure t) :
    truncatedSup (s ⊼ t) a = ⊤ :=
truncatedSup_of_notMem by rwa [coe_infs, lowerClosure_infs]

/--
lemma `truncatedInf_sups_of_notMem` / 引理 `truncatedInf_sups_of_notMem`

English:
lemma truncatedInf_sups_of_notMem
  given: (ha : a ∉ upperClosure s ⊔ upperClosure t)
  proof: truncatedInf_of_notMem by rwa [coe_sups, upperClosure_sups]

中文:
引理 truncatedInf_sups_of_notMem
  条件: (ha : a ∉ upperClosure s ⊔ upperClosure t)
  证明: truncatedInf_of_notMem by rwa [coe_sups, upperClosure_sups]

Depends on / 依赖: coe_sups, truncatedInf_of_notMem, upperClosure_sups
-/
lemma truncatedInf_sups_of_notMem (ha : a ∉ upperClosure s ⊔ upperClosure t) :
    truncatedInf (s ⊻ t) a = ⊥ :=
truncatedInf_of_notMem by rwa [coe_sups, upperClosure_sups]

end DistribLattice

section BooleanAlgebra
variable [BooleanAlgebra α] [DecidableLE α]

/--
lemma `compl_truncatedSup` / 引理 `compl_truncatedSup`

English:
lemma compl_truncatedSup
  given: (s : Finset α) (a : α)
  proof: map_truncatedSup (OrderIso.compl α) _ _

中文:
引理 compl_truncatedSup
  条件: (s : Finset α) (a : α)
  证明: map_truncatedSup (OrderIso.compl α) _ _
-/
@[simp] lemma compl_truncatedSup (s : Finset α) (a : α) :
    (truncatedSup s a)ᶜ = truncatedInf sᶜˢ aᶜ := map_truncatedSup (OrderIso.compl α) _ _

/--
lemma `compl_truncatedInf` / 引理 `compl_truncatedInf`

English:
lemma compl_truncatedInf
  given: (s : Finset α) (a : α)
  proof: map_truncatedInf (OrderIso.compl α) _ _

中文:
引理 compl_truncatedInf
  条件: (s : Finset α) (a : α)
  证明: map_truncatedInf (OrderIso.compl α) _ _
-/
@[simp] lemma compl_truncatedInf (s : Finset α) (a : α) :
    (truncatedInf s a)ᶜ = truncatedSup sᶜˢ aᶜ := map_truncatedInf (OrderIso.compl α) _ _

end BooleanAlgebra

variable [DecidableEq α] [Fintype α]

/--
lemma `card_truncatedSup_union_add_card_truncatedSup_infs` / 引理 `card_truncatedSup_union_add_card_truncatedSup_infs`

English:
lemma card_truncatedSup_union_add_card_truncatedSup_infs
  given: (𝒜 ℬ : Finset (Finset α)) (s : Finset α)
  proof: by
  by_cases h𝒜 : s in lowerClosure (𝒜 : Set <| Finset α) <;>
    by_cases hℬ : s in lowerClosure (ℬ : Set <| Finset α)
  · rw [truncatedSup_union h𝒜 hℬ, truncatedSup_infs h𝒜 hℬ]
    exact card_union_add_card_inter _ _
  · rw [truncatedSup_union_left h𝒜 hℬ, truncatedSup_of_notMem hℬ,
      truncate

中文:
引理 card_truncatedSup_union_add_card_truncatedSup_infs
  条件: (𝒜 ℬ : Finset (Finset α)) (s : Finset α)
  证明: by
  by_cases h𝒜 : s in lowerClosure (𝒜 : Set <| Finset α) <;>
    by_cases hℬ : s in lowerClosure (ℬ : Set <| Finset α)
  · rw [truncatedSup_union h𝒜 hℬ, truncatedSup_infs h𝒜 hℬ]
    exact card_union_add_card_inter _ _
  · rw [truncatedSup_union_left h𝒜 hℬ, truncatedSup_of_notMem hℬ,
      truncate

Depends on / 依赖: Finset, add_comm, card_union_add_card_inter, lowerClosure, truncatedSup_infs, truncatedSup_infs_of_notMem, truncatedSup_of_notMem, truncatedSup_union, truncatedSup_union_left, truncatedSup_union_right
-/
lemma card_truncatedSup_union_add_card_truncatedSup_infs (𝒜 ℬ : Finset (Finset α)) (s : Finset α) :
    #(truncatedSup (𝒜 union ℬ) s) + #(truncatedSup (𝒜 ⊼ ℬ) s) =
      #(truncatedSup 𝒜 s) + #(truncatedSup ℬ s) := by
  by_cases h𝒜 : s in lowerClosure (𝒜 : Set <| Finset α) <;>
    by_cases hℬ : s in lowerClosure (ℬ : Set <| Finset α)
  · rw [truncatedSup_union h𝒜 hℬ, truncatedSup_infs h𝒜 hℬ]
    exact card_union_add_card_inter _ _
  · rw [truncatedSup_union_left h𝒜 hℬ, truncatedSup_of_notMem hℬ,
      truncatedSup_infs_of_notMem fun h => hℬ h.2]
  · rw [truncatedSup_union_right h𝒜 hℬ, truncatedSup_of_notMem h𝒜,
      truncatedSup_infs_of_notMem fun h => h𝒜 h.1, add_comm]
  · rw [truncatedSup_of_notMem h𝒜, truncatedSup_of_notMem hℬ,
      truncatedSup_union_of_notMem h𝒜 hℬ, truncatedSup_infs_of_notMem fun h => h𝒜 h.1]

/--
lemma `card_truncatedInf_union_add_card_truncatedInf_sups` / 引理 `card_truncatedInf_union_add_card_truncatedInf_sups`

English:
lemma card_truncatedInf_union_add_card_truncatedInf_sups
  given: (𝒜 ℬ : Finset (Finset α)) (s : Finset α)
  proof: by
  by_cases h𝒜 : s in upperClosure (𝒜 : Set <| Finset α) <;>
    by_cases hℬ : s in upperClosure (ℬ : Set <| Finset α)
  · rw [truncatedInf_union h𝒜 hℬ, truncatedInf_sups h𝒜 hℬ]
    exact card_inter_add_card_union _ _
  · rw [truncatedInf_union_left h𝒜 hℬ, truncatedInf_of_notMem hℬ,
      truncate

中文:
引理 card_truncatedInf_union_add_card_truncatedInf_sups
  条件: (𝒜 ℬ : Finset (Finset α)) (s : Finset α)
  证明: by
  by_cases h𝒜 : s in upperClosure (𝒜 : Set <| Finset α) <;>
    by_cases hℬ : s in upperClosure (ℬ : Set <| Finset α)
  · rw [truncatedInf_union h𝒜 hℬ, truncatedInf_sups h𝒜 hℬ]
    exact card_inter_add_card_union _ _
  · rw [truncatedInf_union_left h𝒜 hℬ, truncatedInf_of_notMem hℬ,
      truncate

Depends on / 依赖: Finset, add_comm, card_inter_add_card_union, truncatedInf_of_notMem, truncatedInf_sups, truncatedInf_sups_of_notMem, truncatedInf_union, truncatedInf_union_left, truncatedInf_union_right, upperClosure
-/
lemma card_truncatedInf_union_add_card_truncatedInf_sups (𝒜 ℬ : Finset (Finset α)) (s : Finset α) :
    #(truncatedInf (𝒜 union ℬ) s) + #(truncatedInf (𝒜 ⊻ ℬ) s) =
      #(truncatedInf 𝒜 s) + #(truncatedInf ℬ s) := by
  by_cases h𝒜 : s in upperClosure (𝒜 : Set <| Finset α) <;>
    by_cases hℬ : s in upperClosure (ℬ : Set <| Finset α)
  · rw [truncatedInf_union h𝒜 hℬ, truncatedInf_sups h𝒜 hℬ]
    exact card_inter_add_card_union _ _
  · rw [truncatedInf_union_left h𝒜 hℬ, truncatedInf_of_notMem hℬ,
      truncatedInf_sups_of_notMem fun h => hℬ h.2]
  · rw [truncatedInf_union_right h𝒜 hℬ, truncatedInf_of_notMem h𝒜,
      truncatedInf_sups_of_notMem fun h => h𝒜 h.1, add_comm]
  · rw [truncatedInf_of_notMem h𝒜, truncatedInf_of_notMem hℬ,
      truncatedInf_union_of_notMem h𝒜 hℬ, truncatedInf_sups_of_notMem fun h => h𝒜 h.1]

end Finset

open Finset hiding card
open Fintype Nat

namespace AhlswedeZhang
variable {α : Type*} [Fintype α] [DecidableEq α] {𝒜 : Finset (Finset α)} {s : Finset α}

/--
Definition of `infSum` / `infSum` 的定义

English:
definition infSum
  signature: (𝒜 : Finset (Finset α))
  body: ∑ s, #(truncatedInf 𝒜 s) / (#s * (card α).choose #s)

中文:
定义 infSum
  签名: (𝒜 : Finset (Finset α))
  定义体: ∑ s, #(truncatedInf 𝒜 s) / (#s * (card α).choose #s)

Depends on / 依赖: truncatedInf
-/
def infSum (𝒜 : Finset (Finset α)) : Rat :=
  ∑ s, #(truncatedInf 𝒜 s) / (#s * (card α).choose #s)

/--
Definition of `supSum` / `supSum` 的定义

English:
definition supSum
  signature: (𝒜 : Finset (Finset α))
  body: ∑ s, #(truncatedSup 𝒜 s) / ((card α - #s) * (card α).choose #s)

中文:
定义 supSum
  签名: (𝒜 : Finset (Finset α))
  定义体: ∑ s, #(truncatedSup 𝒜 s) / ((card α - #s) * (card α).choose #s)

Depends on / 依赖: truncatedSup
-/
def supSum (𝒜 : Finset (Finset α)) : Rat :=
  ∑ s, #(truncatedSup 𝒜 s) / ((card α - #s) * (card α).choose #s)

/--
lemma `supSum_union_add_supSum_infs` / 引理 `supSum_union_add_supSum_infs`

English:
lemma supSum_union_add_supSum_infs
  given: (𝒜 ℬ : Finset (Finset α))
  proof: by
  unfold supSum
  rw [← sum_add_distrib]; rw [← sum_add_distrib]; rw [Finset.sum_congr rfl fun s _ => _]
  simp_rw [← add_div, ← Nat.cast_add, card_truncatedSup_union_add_card_truncatedSup_infs]
  simp

中文:
引理 supSum_union_add_supSum_infs
  条件: (𝒜 ℬ : Finset (Finset α))
  证明: by
  unfold supSum
  rw [← sum_add_distrib]; rw [← sum_add_distrib]; rw [Finset.sum_congr rfl fun s _ => _]
  simp_rw [← add_div, ← Nat.cast_add, card_truncatedSup_union_add_card_truncatedSup_infs]
  simp

Depends on / 依赖: Finset, Finset.sum_congr, Nat.cast_add, add_div, card_truncatedSup_union_add_card_truncatedSup_infs, cast_add, simp_rw, sum_add_distrib, sum_congr, supSum
-/
lemma supSum_union_add_supSum_infs (𝒜 ℬ : Finset (Finset α)) :
    supSum (𝒜 union ℬ) + supSum (𝒜 ⊼ ℬ) = supSum 𝒜 + supSum ℬ := by
  unfold supSum
  rw [← sum_add_distrib]; rw [← sum_add_distrib]; rw [Finset.sum_congr rfl fun s _ => _]
  simp_rw [← add_div, ← Nat.cast_add, card_truncatedSup_union_add_card_truncatedSup_infs]
  simp

/--
lemma `infSum_union_add_infSum_sups` / 引理 `infSum_union_add_infSum_sups`

English:
lemma infSum_union_add_infSum_sups
  given: (𝒜 ℬ : Finset (Finset α))
  proof: by
  unfold infSum
  rw [← sum_add_distrib]; rw [← sum_add_distrib]; rw [Finset.sum_congr rfl fun s _ => _]
  simp_rw [← add_div, ← Nat.cast_add, card_truncatedInf_union_add_card_truncatedInf_sups]
  simp

中文:
引理 infSum_union_add_infSum_sups
  条件: (𝒜 ℬ : Finset (Finset α))
  证明: by
  unfold infSum
  rw [← sum_add_distrib]; rw [← sum_add_distrib]; rw [Finset.sum_congr rfl fun s _ => _]
  simp_rw [← add_div, ← Nat.cast_add, card_truncatedInf_union_add_card_truncatedInf_sups]
  simp

Depends on / 依赖: Finset, Finset.sum_congr, Nat.cast_add, add_div, card_truncatedInf_union_add_card_truncatedInf_sups, cast_add, infSum, simp_rw, sum_add_distrib, sum_congr
-/
lemma infSum_union_add_infSum_sups (𝒜 ℬ : Finset (Finset α)) :
    infSum (𝒜 union ℬ) + infSum (𝒜 ⊻ ℬ) = infSum 𝒜 + infSum ℬ := by
  unfold infSum
  rw [← sum_add_distrib]; rw [← sum_add_distrib]; rw [Finset.sum_congr rfl fun s _ => _]
  simp_rw [← add_div, ← Nat.cast_add, card_truncatedInf_union_add_card_truncatedInf_sups]
  simp

/--
lemma `IsAntichain.le_infSum` / 引理 `IsAntichain.le_infSum`

English:
lemma IsAntichain.le_infSum
  given: (h𝒜 : IsAntichain (· subseteq ·) (𝒜 : Set (Finset α))) (h𝒜₀ : ∅ ∉ 𝒜)
  proof: by
  calc
    _ = ∑ s in 𝒜, #(truncatedInf 𝒜 s) / (#s * (card α).choose #s : Rat) := ?_
    _ <= _ := sum_le_univ_sum_of_nonneg fun s => by positivity
  refine sum_congr rfl fun s hs => ?_
  rw [truncatedInf_of_isAntichain h𝒜 hs]; rw [div_mul_cancel_left₀]
  have := (nonempty_iff_ne_empty.2 <| ne_of

中文:
引理 IsAntichain.le_infSum
  条件: (h𝒜 : IsAntichain (· subseteq ·) (𝒜 : Set (Finset α))) (h𝒜₀ : ∅ ∉ 𝒜)
  证明: by
  calc
    _ = ∑ s in 𝒜, #(truncatedInf 𝒜 s) / (#s * (card α).choose #s : Rat) := ?_
    _ <= _ := sum_le_univ_sum_of_nonneg fun s => by positivity
  refine sum_congr rfl fun s hs => ?_
  rw [truncatedInf_of_isAntichain h𝒜 hs]; rw [div_mul_cancel_left₀]
  have := (nonempty_iff_ne_empty.2 <| ne_of

Depends on / 依赖: card_pos, ne_of_mem_of_not_mem, nonempty_iff_ne_empty, sum_congr, sum_le_univ_sum_of_nonneg, truncatedInf, truncatedInf_of_isAntichain
-/
lemma IsAntichain.le_infSum (h𝒜 : IsAntichain (· subseteq ·) (𝒜 : Set (Finset α))) (h𝒜₀ : ∅ ∉ 𝒜) :
    ∑ s in 𝒜, ((card α).choose #s : Rat)⁻¹ <= infSum 𝒜 := by
  calc
    _ = ∑ s in 𝒜, #(truncatedInf 𝒜 s) / (#s * (card α).choose #s : Rat) := ?_
    _ <= _ := sum_le_univ_sum_of_nonneg fun s => by positivity
  refine sum_congr rfl fun s hs => ?_
  rw [truncatedInf_of_isAntichain h𝒜 hs]; rw [div_mul_cancel_left₀]
  have := (nonempty_iff_ne_empty.2 <| ne_of_mem_of_not_mem hs h𝒜₀).card_pos
  positivity

variable [Nonempty α]

/--
lemma `supSum_singleton` / 引理 `supSum_singleton`

English:
lemma supSum_singleton
  given: (hs : s != univ)
  proof: by
  have : forall t : Finset α,
    (card α - #(truncatedSup {s} t) : Rat) / ((card α - #t) * (card α).choose #t) =
    if t subseteq s then (card α - #s : Rat) / ((card α - #t) * (card α).choose #t) else 0 := by
    rintro t
    simp_rw [truncatedSup_singleton]
    split_ifs <;> simp
  simp_rw [← 

中文:
引理 supSum_singleton
  条件: (hs : s != univ)
  证明: by
  have : forall t : Finset α,
    (card α - #(truncatedSup {s} t) : Rat) / ((card α - #t) * (card α).choose #t) =
    if t subseteq s then (card α - #s : Rat) / ((card α - #t) * (card α).choose #t) else 0 := by
    rintro t
    simp_rw [truncatedSup_singleton]
    split_ifs <;> simp
  simp_rw [← 
-/
@[simp] lemma supSum_singleton (hs : s != univ) :
    supSum ({s} : Finset (Finset α)) = card α * ∑ k in range (card α), (k : Rat)⁻¹ := by
  have : forall t : Finset α,
    (card α - #(truncatedSup {s} t) : Rat) / ((card α - #t) * (card α).choose #t) =
    if t subseteq s then (card α - #s : Rat) / ((card α - #t) * (card α).choose #t) else 0 := by
    rintro t
    simp_rw [truncatedSup_singleton]
    split_ifs <;> simp
  simp_rw [← sub_eq_of_eq_add (Fintype.sum_div_mul_card_choose_card α), eq_sub_iff_add_eq,
    ← eq_sub_iff_add_eq', supSum, ← sum_sub_distrib, ← sub_div]
  rw [sum_congr rfl fun t _ => this t]; rw [sum_ite]; rw [sum_const_zero]; rw [add_zero]; rw [filter_subset_univ]; rw [sum_powerset]; rw [← binomial_sum_eq ((card_lt_iff_ne_univ _).2 hs)]; rw [eq_comm]
  refine sum_congr rfl fun n _ => ?_
  rw [mul_div_assoc]; rw [← nsmul_eq_mul]
  exact sum_powersetCard n s fun m => (card α - #s : Rat) / ((card α - m) * (card α).choose m)

/--
lemma `infSum_compls_add_supSum` / 引理 `infSum_compls_add_supSum`

English:
lemma infSum_compls_add_supSum
  given: (𝒜 : Finset (Finset α))
  proof: by
  unfold infSum supSum
  rw [← @map_univ_of_surjective (Finset α) _ _ _ ⟨compl]; rw [compl_injective⟩ compl_surjective]; rw [sum_map]
  simp only [Function.Embedding.coeFn_mk, univ_map_embedding, ← compl_truncatedSup,
    ← sum_add_distrib, card_compl, cast_sub (card_le_univ _), choose_symm (card

中文:
引理 infSum_compls_add_supSum
  条件: (𝒜 : Finset (Finset α))
  证明: by
  unfold infSum supSum
  rw [← @map_univ_of_surjective (Finset α) _ _ _ ⟨compl]; rw [compl_injective⟩ compl_surjective]; rw [sum_map]
  simp only [Function.Embedding.coeFn_mk, univ_map_embedding, ← compl_truncatedSup,
    ← sum_add_distrib, card_compl, cast_sub (card_le_univ _), choose_symm (card

Depends on / 依赖: Embedding, Finset, Fintype, Fintype.sum_div_mul_card_choose_card, Function, Function.Embedding.coeFn_mk, add_div, card_compl, card_le_univ, cast_sub, choose_symm, coeFn_mk, compl_injective, compl_surjective, compl_truncatedSup, infSum, map_univ_of_surjective, sub_add_cancel, sum_add_distrib, sum_div_mul_card_choose_card
-/
lemma infSum_compls_add_supSum (𝒜 : Finset (Finset α)) :
    infSum 𝒜ᶜˢ + supSum 𝒜 = card α * ∑ k in range (card α), (k : Rat)⁻¹ + 1 := by
  unfold infSum supSum
  rw [← @map_univ_of_surjective (Finset α) _ _ _ ⟨compl]; rw [compl_injective⟩ compl_surjective]; rw [sum_map]
  simp only [Function.Embedding.coeFn_mk, univ_map_embedding, ← compl_truncatedSup,
    ← sum_add_distrib, card_compl, cast_sub (card_le_univ _), choose_symm (card_le_univ _),
    ← add_div, sub_add_cancel, Fintype.sum_div_mul_card_choose_card]

/--
lemma `supSum_of_univ_notMem` / 引理 `supSum_of_univ_notMem`

English:
lemma supSum_of_univ_notMem
  given: (h𝒜₁ : 𝒜.Nonempty) (h𝒜₂ : univ ∉ 𝒜)
  proof: by
  set m := 𝒜.card with hm
  clear_value m
  induction m using Nat.strongRecOn generalizing 𝒜 with | ind m ih => _
  replace ih := fun 𝒜 h𝒜 h𝒜₁ h𝒜₂ => @ih _ h𝒜 𝒜 h𝒜₁ h𝒜₂ rfl
  obtain ⟨a, rfl⟩ | h𝒜₃ := h𝒜₁.exists_eq_singleton_or_nontrivial
  · refine supSum_singleton ?_
    simpa [eq_comm] using h𝒜

中文:
引理 supSum_of_univ_notMem
  条件: (h𝒜₁ : 𝒜.Nonempty) (h𝒜₂ : univ ∉ 𝒜)
  证明: by
  set m := 𝒜.card with hm
  clear_value m
  induction m using Nat.strongRecOn generalizing 𝒜 with | ind m ih => _
  replace ih := fun 𝒜 h𝒜 h𝒜₁ h𝒜₂ => @ih _ h𝒜 𝒜 h𝒜₁ h𝒜₂ rfl
  obtain ⟨a, rfl⟩ | h𝒜₃ := h𝒜₁.exists_eq_singleton_or_nontrivial
  · refine supSum_singleton ?_
    simpa [eq_comm] using h𝒜

Depends on / 依赖: Nat.strongRecOn, Nonempty, card_eq_succ, card_pos, card_pos.ne, clear_value, eq_comm, eq_sub_of_add_eq, exists_eq_singleton_or_nontrivial, generalizing, hm.symm, insert_eq, replace, strongRecOn, supSum_singleton, supSum_union_add_supSum_infs
-/
lemma supSum_of_univ_notMem (h𝒜₁ : 𝒜.Nonempty) (h𝒜₂ : univ ∉ 𝒜) :
    supSum 𝒜 = card α * ∑ k in range (card α), (k : Rat)⁻¹ := by
  set m := 𝒜.card with hm
  clear_value m
  induction m using Nat.strongRecOn generalizing 𝒜 with | ind m ih => _
  replace ih := fun 𝒜 h𝒜 h𝒜₁ h𝒜₂ => @ih _ h𝒜 𝒜 h𝒜₁ h𝒜₂ rfl
  obtain ⟨a, rfl⟩ | h𝒜₃ := h𝒜₁.exists_eq_singleton_or_nontrivial
  · refine supSum_singleton ?_
    simpa [eq_comm] using h𝒜₂
  cases m
  · cases h𝒜₁.card_pos.ne hm
  obtain ⟨s, 𝒜, hs, rfl, rfl⟩ := card_eq_succ.1 hm.symm
  have h𝒜 : 𝒜.Nonempty := by by_contra! rfl; simp at h𝒜₃
  rw [insert_eq]; rw [eq_sub_of_add_eq (supSum_union_add_supSum_infs _ _)]; rw [singleton_infs]; rw [supSum_singleton (ne_of_mem_of_not_mem (mem_insert_self _ _) h𝒜₂)]; rw [ih]; rw [ih]; rw [add_sub_cancel_right]
  · exact card_image_le.trans_lt (lt_add_one _)
  · exact h𝒜.image _
  · simpa using fun _ => ne_of_mem_of_not_mem (mem_insert_self _ _) h𝒜₂
  · exact lt_add_one _
  · exact h𝒜
  · exact fun h => h𝒜₂ (mem_insert_of_mem h)

/--
lemma `infSum_eq_one` / 引理 `infSum_eq_one`

English:
lemma infSum_eq_one
  given: (h𝒜₁ : 𝒜.Nonempty) (h𝒜₀ : ∅ ∉ 𝒜)
  statement: infSum 𝒜 = 1
  proof: by
  rw [← compls_compls 𝒜]; rw [eq_sub_of_add_eq (infSum_compls_add_supSum _)]; rw [supSum_of_univ_notMem h𝒜₁.compls]; rw [add_sub_cancel_left]
  simpa

中文:
引理 infSum_eq_one
  条件: (h𝒜₁ : 𝒜.Nonempty) (h𝒜₀ : ∅ ∉ 𝒜)
  结论: infSum 𝒜 = 1
  证明: by
  rw [← compls_compls 𝒜]; rw [eq_sub_of_add_eq (infSum_compls_add_supSum _)]; rw [supSum_of_univ_notMem h𝒜₁.compls]; rw [add_sub_cancel_left]
  simpa

Depends on / 依赖: add_sub_cancel_left, compls, compls_compls, eq_sub_of_add_eq, infSum_compls_add_supSum, supSum_of_univ_notMem
-/
lemma infSum_eq_one (h𝒜₁ : 𝒜.Nonempty) (h𝒜₀ : ∅ ∉ 𝒜) : infSum 𝒜 = 1 := by
  rw [← compls_compls 𝒜]; rw [eq_sub_of_add_eq (infSum_compls_add_supSum _)]; rw [supSum_of_univ_notMem h𝒜₁.compls]; rw [add_sub_cancel_left]
  simpa

end AhlswedeZhang
