/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Finset.Sups
public import Mathlib.Order.Birkhoff
public import Mathlib.Order.Booleanisation
public import Mathlib.Order.Sublattice
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.GCongr

/-!
# The four functions theorem and corollaries

This file proves the four functions theorem. The statement is that if
`f₁ a * f₂ b ≤ f₃ (a ⊓ b) * f₄ (a ⊔ b)` for all `a`, `b` in a finite distributive lattice, then
`(∑ x ∈ s, f₁ x) * (∑ x ∈ t, f₂ x) ≤ (∑ x ∈ s ⊼ t, f₃ x) * (∑ x ∈ s ⊻ t, f₄ x)` where
`s ⊼ t = {a ⊓ b | a ∈ s, b ∈ t}`, `s ⊻ t = {a ⊔ b | a ∈ s, b ∈ t}`.

The proof uses Birkhoff's representation theorem to restrict to the case where the finite
distributive lattice is in fact a finite powerset algebra, namely `Finset α` for some finite `α`.
Then it proves this new statement by induction on the size of `α`.

## Main declarations

The two versions of the four functions theorem are
* `Finset.four_functions_theorem` for finite powerset algebras.
* `four_functions_theorem` for any finite distributive lattices.

We deduce a number of corollaries:
* `Finset.le_card_infs_mul_card_sups`: Daykin inequality. `|s| |t| ≤ |s ⊼ t| |s ⊻ t|`
* `holley`: Holley inequality.
* `fkg`: Fortuin-Kasteleyn-Ginibre inequality.
* `Finset.card_le_card_diffs`: Marica-Schönheim inequality. `|s| ≤ |{a \ b | a, b ∈ s}|`

## TODO

Prove that lattices in which `Finset.le_card_infs_mul_card_sups` holds are distributive. See
Daykin, *A lattice is distributive iff |A| |B| <= |A ∨ B| |A ∧ B|*

Prove the Fishburn-Shepp inequality.

Is `collapse` a construct generally useful for set family inductions? If so, we should move it to an
earlier file and give it a proper API.

## References

[*Applications of the FKG Inequality and Its Relatives*, Graham][Graham1983]
-/

public section

open Finset Fintype Function
open scoped FinsetFamily

variable {α β : Type*}

section Finset
variable [DecidableEq α] [CommSemiring β] [LinearOrder β] [IsStrictOrderedRing β]
  {𝒜 : Finset (Finset α)} {a : α} {f f₁ f₂ f₃ f₄ : Finset α -> β} {s t u : Finset α}

/--
lemma `ineq` / 引理 `ineq`

English:
lemma ineq
  statement: [ExistsAddOfLE β] {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : β}
  proof: by
  calc
    _ = a₀ * b₀ + (a₀ * b₁ + a₁ * b₀) + a₁ * b₁ := by ring
    _ <= c₀ * d₀ + (c₀ * d₁ + c₁ * d₀) + c₁ * d₁ := add_le_add_three h₀₀ ?_ h₁₁
    _ = (c₀ + c₁) * (d₀ + d₁) := by ring
  obtain hcd | hcd := (mul_nonneg hc₀ hd₁).eq_or_lt'
  · rw [hcd] at h₀₁ h₁₀
    rw [h₀₁.antisymm]; rw [h₁₀.antisymm]; rw [add_zero] <;> positivity
  refine le_of_mul_le_mul_right ?_ hcd
  calc (a₀ * b₁ + a₁ * b₀) * (c₀ * d₁)
      = a₀ * b₁ * (c₀ * d₁) + c₀ * d₁ * (a₁ * b₀) := by ring
    _ <= a₀ * b₁ * (a₁ * b₀) + c₀ * d₁ * (c₀ * d₁) := mul_add_mul_le_mul_add_mul h₀₁ h₁₀
    _ = a₀ * b₀ * (a₁ * b₁) + c₀ * d₁ * (c₀ * d₁) := by ring
    _ <= c₀ * d₀ * (c₁ * d₁) + c₀ * d₁ * (c₀ * d₁) := by gcongr
    _ = (c₀ * d₁ + c₁ * d₀) * (c₀ * d₁) := by ring

中文:
引理 ineq
  结论: [ExistsAddOfLE β] {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : β}
  证明: by
  calc
    _ = a₀ * b₀ + (a₀ * b₁ + a₁ * b₀) + a₁ * b₁ := by ring
    _ <= c₀ * d₀ + (c₀ * d₁ + c₁ * d₀) + c₁ * d₁ := add_le_add_three h₀₀ ?_ h₁₁
    _ = (c₀ + c₁) * (d₀ + d₁) := by ring
  obtain hcd | hcd := (mul_nonneg hc₀ hd₁).eq_or_lt'
  · rw [hcd] at h₀₁ h₁₀
    rw [h₀₁.antisymm]; rw [h₁₀.antisymm]; rw [add_zero] <;> positivity
  refine le_of_mul_le_mul_right ?_ hcd
  calc (a₀ * b₁ + a₁ * b₀) * (c₀ * d₁)
      = a₀ * b₁ * (c₀ * d₁) + c₀ * d₁ * (a₁ * b₀) := by ring
    _ <= a₀ * b₁ * (a₁ * b₀) + c₀ * d₁ * (c₀ * d₁) := mul_add_mul_le_mul_add_mul h₀₁ h₁₀
    _ = a₀ * b₀ * (a₁ * b₁) + c₀ * d₁ * (c₀ * d₁) := by ring
    _ <= c₀ * d₀ * (c₁ * d₁) + c₀ * d₁ * (c₀ * d₁) := by gcongr
    _ = (c₀ * d₁ + c₁ * d₀) * (c₀ * d₁) := by ring
-/
private lemma ineq [ExistsAddOfLE β] {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : β}
    (ha₀ : 0 <= a₀) (ha₁ : 0 <= a₁) (hb₀ : 0 <= b₀) (hb₁ : 0 <= b₁)
    (hc₀ : 0 <= c₀) (hc₁ : 0 <= c₁) (hd₀ : 0 <= d₀) (hd₁ : 0 <= d₁)
    (h₀₀ : a₀ * b₀ <= c₀ * d₀) (h₁₀ : a₁ * b₀ <= c₀ * d₁)
    (h₀₁ : a₀ * b₁ <= c₀ * d₁) (h₁₁ : a₁ * b₁ <= c₁ * d₁) :
    (a₀ + a₁) * (b₀ + b₁) <= (c₀ + c₁) * (d₀ + d₁) := by
  calc
    _ = a₀ * b₀ + (a₀ * b₁ + a₁ * b₀) + a₁ * b₁ := by ring
    _ <= c₀ * d₀ + (c₀ * d₁ + c₁ * d₀) + c₁ * d₁ := add_le_add_three h₀₀ ?_ h₁₁
    _ = (c₀ + c₁) * (d₀ + d₁) := by ring
  obtain hcd | hcd := (mul_nonneg hc₀ hd₁).eq_or_lt'
  · rw [hcd] at h₀₁ h₁₀
    rw [h₀₁.antisymm]; rw [h₁₀.antisymm]; rw [add_zero] <;> positivity
  refine le_of_mul_le_mul_right ?_ hcd
  calc (a₀ * b₁ + a₁ * b₀) * (c₀ * d₁)
      = a₀ * b₁ * (c₀ * d₁) + c₀ * d₁ * (a₁ * b₀) := by ring
    _ <= a₀ * b₁ * (a₁ * b₀) + c₀ * d₁ * (c₀ * d₁) := mul_add_mul_le_mul_add_mul h₀₁ h₁₀
    _ = a₀ * b₀ * (a₁ * b₁) + c₀ * d₁ * (c₀ * d₁) := by ring
    _ <= c₀ * d₀ * (c₁ * d₁) + c₀ * d₁ * (c₀ * d₁) := by gcongr
    _ = (c₀ * d₁ + c₁ * d₀) * (c₀ * d₁) := by ring

set_option backward.privateInPublic true in
/--
Definition of `collapse` / `collapse` 的定义

English:
definition collapse
  signature: (𝒜 : Finset (Finset α)) (a : α) (f : Finset α -> β) (s : Finset α)
  body: ∑ t in 𝒜 with t.erase a = s, f t

中文:
定义 collapse
  签名: (𝒜 : 有限集 (有限集 α)) (a : α) (f : 有限集 α -> β) (s : 有限集 α)
  定义体: ∑ t in 𝒜 with t.erase a = s, f t
-/
private def collapse (𝒜 : Finset (Finset α)) (a : α) (f : Finset α -> β) (s : Finset α) : β :=
  ∑ t in 𝒜 with t.erase a = s, f t

/--
lemma `erase_eq_iff` / 引理 `erase_eq_iff`

English:
lemma erase_eq_iff
  given: (hs : a ∉ s)
  statement: t.erase a = s ↔ t = s ∨ t = insert a s
  proof: by
  grind

中文:
引理 erase_eq_iff
  条件: (hs : a ∉ s)
  结论: t.erase a = s ↔ t = s ∨ t = insert a s
  证明: by
  grind
-/
private lemma erase_eq_iff (hs : a ∉ s) : t.erase a = s ↔ t = s ∨ t = insert a s := by
  grind

/--
lemma `filter_collapse_eq` / 引理 `filter_collapse_eq`

English:
lemma filter_collapse_eq
  given: (ha : a ∉ s) (𝒜 : Finset (Finset α))
  proof: by
  ext t; split_ifs <;> simp [erase_eq_iff ha] <;> aesop

中文:
引理 filter_collapse_eq
  条件: (ha : a ∉ s) (𝒜 : 有限集 (有限集 α))
  证明: by
  ext t; split_ifs <;> simp [erase_eq_iff ha] <;> aesop
-/
private lemma filter_collapse_eq (ha : a ∉ s) (𝒜 : Finset (Finset α)) :
    {t in 𝒜 | t.erase a = s} =
      if s in 𝒜 then
        (if insert a s in 𝒜 then {s, insert a s} else {s})
      else
        (if insert a s in 𝒜 then {insert a s} else ∅) := by
  ext t; split_ifs <;> simp [erase_eq_iff ha] <;> aesop

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
omit [LinearOrder β] [IsStrictOrderedRing β] in
/--
lemma `collapse_eq` / 引理 `collapse_eq`

English:
lemma collapse_eq
  given: (ha : a ∉ s) (𝒜 : Finset (Finset α)) (f : Finset α -> β)
  proof: by
  rw [collapse]; rw [filter_collapse_eq ha]
  split_ifs <;> simp [(ne_of_mem_of_not_mem' (mem_insert_self a s) ha).symm, *]

中文:
引理 collapse_eq
  条件: (ha : a ∉ s) (𝒜 : 有限集 (有限集 α)) (f : 有限集 α -> β)
  证明: by
  rw [collapse]; rw [filter_collapse_eq ha]
  split_ifs <;> simp [(ne_of_mem_of_not_mem' (mem_insert_self a s) ha).symm, *]

Depends on / 依赖: collapse, filter_collapse_eq, mem_insert_self, ne_of_mem_of_not_mem, split_ifs
-/
lemma collapse_eq (ha : a ∉ s) (𝒜 : Finset (Finset α)) (f : Finset α -> β) :
    collapse 𝒜 a f s = (if s in 𝒜 then f s else 0) +
      if insert a s in 𝒜 then f (insert a s) else 0 := by
  rw [collapse]; rw [filter_collapse_eq ha]
  split_ifs <;> simp [(ne_of_mem_of_not_mem' (mem_insert_self a s) ha).symm, *]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
omit [LinearOrder β] [IsStrictOrderedRing β] in
/--
lemma `collapse_of_mem` / 引理 `collapse_of_mem`

English:
lemma collapse_of_mem
  statement: (ha : a ∉ s) (ht : t in 𝒜) (hu : u in 𝒜) (hts : t = s)
  proof: by
  subst hts; subst hus; simp_rw [collapse_eq ha, if_pos ht, if_pos hu]

中文:
引理 collapse_of_mem
  结论: (ha : a ∉ s) (ht : t in 𝒜) (hu : u in 𝒜) (hts : t = s)
  证明: by
  subst hts; subst hus; simp_rw [collapse_eq ha, if_pos ht, if_pos hu]

Depends on / 依赖: collapse_eq, if_pos, simp_rw
-/
lemma collapse_of_mem (ha : a ∉ s) (ht : t in 𝒜) (hu : u in 𝒜) (hts : t = s)
    (hus : u = insert a s) : collapse 𝒜 a f s = f t + f u := by
  subst hts; subst hus; simp_rw [collapse_eq ha, if_pos ht, if_pos hu]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
lemma `le_collapse_of_mem` / 引理 `le_collapse_of_mem`

English:
lemma le_collapse_of_mem
  given: (ha : a ∉ s) (hf : 0 <= f) (hts : t = s) (ht : t in 𝒜)
  proof: by
  subst hts
  rw [collapse_eq ha]; rw [if_pos ht]
  split_ifs
· exact le_add_of_nonneg_right hf _
  · rw [add_zero]

中文:
引理 le_collapse_of_mem
  条件: (ha : a ∉ s) (hf : 0 <= f) (hts : t = s) (ht : t in 𝒜)
  证明: by
  subst hts
  rw [collapse_eq ha]; rw [if_pos ht]
  split_ifs
· exact le_add_of_nonneg_right hf _
  · rw [add_zero]

Depends on / 依赖: add_zero, collapse_eq, if_pos, le_add_of_nonneg_right, split_ifs
-/
lemma le_collapse_of_mem (ha : a ∉ s) (hf : 0 <= f) (hts : t = s) (ht : t in 𝒜) :
    f t <= collapse 𝒜 a f s := by
  subst hts
  rw [collapse_eq ha]; rw [if_pos ht]
  split_ifs
· exact le_add_of_nonneg_right hf _
  · rw [add_zero]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
lemma `le_collapse_of_insert_mem` / 引理 `le_collapse_of_insert_mem`

English:
lemma le_collapse_of_insert_mem
  given: (ha : a ∉ s) (hf : 0 <= f) (hts : t = insert a s) (ht : t in 𝒜)
  proof: by
  rw [collapse_eq ha]; rw [← hts]; rw [if_pos ht]
  split_ifs
· exact le_add_of_nonneg_left hf _
  · rw [zero_add]

中文:
引理 le_collapse_of_insert_mem
  条件: (ha : a ∉ s) (hf : 0 <= f) (hts : t = insert a s) (ht : t in 𝒜)
  证明: by
  rw [collapse_eq ha]; rw [← hts]; rw [if_pos ht]
  split_ifs
· exact le_add_of_nonneg_left hf _
  · rw [zero_add]

Depends on / 依赖: collapse_eq, if_pos, le_add_of_nonneg_left, split_ifs, zero_add
-/
lemma le_collapse_of_insert_mem (ha : a ∉ s) (hf : 0 <= f) (hts : t = insert a s) (ht : t in 𝒜) :
    f t <= collapse 𝒜 a f s := by
  rw [collapse_eq ha]; rw [← hts]; rw [if_pos ht]
  split_ifs
· exact le_add_of_nonneg_left hf _
  · rw [zero_add]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
lemma `collapse_nonneg` / 引理 `collapse_nonneg`

English:
lemma collapse_nonneg
  given: (hf : 0 <= f)
  statement: 0 <= collapse 𝒜 a f
  proof: fun _s => sum_nonneg fun _t _ => hf _

中文:
引理 collapse_nonneg
  条件: (hf : 0 <= f)
  结论: 0 <= collapse 𝒜 a f
  证明: fun _s => sum_nonneg fun _t _ => hf _

Depends on / 依赖: sum_nonneg
-/
lemma collapse_nonneg (hf : 0 <= f) : 0 <= collapse 𝒜 a f := fun _s => sum_nonneg fun _t _ => hf _

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
lemma `collapse_modular` / 引理 `collapse_modular`

English:
lemma collapse_modular
  statement: [ExistsAddOfLE β]
  proof: by
  rintro s hsu t htu
  -- Gather a bunch of facts we'll need a lot
have := hsu.trans subset_insert a _
have := htu.trans subset_insert a _
  have := insert_subset_insert a hsu
  have := insert_subset_insert a htu
  have has := notMem_mono hsu hu
  have hat := notMem_mono htu hu
  have : a ∉ s inter t := notMem_mono (inter_subset_left.trans hsu) hu
  have := notMem_union.2 ⟨has, hat⟩
  rw [collapse_eq has]
  split_ifs
  · rw [collapse_eq hat]
    split_ifs
    · rw [collapse_of_mem ‹_› (inter_mem_infs ‹_› ‹_›) (inter_mem_infs ‹_› ‹_›) rfl
        (insert_inter_distrib _ _ _).symm, collapse_of_mem ‹_› (union_mem_sups ‹_› ‹_›)
        (union_mem_sups ‹_› ‹_›) rfl (insert_union_distrib _ _ _).symm]
      refine ineq (h₁ _) (h₁ _) (h₂ _) (h₂ _) (h₃ _) (h₃ _) (h₄ _) (h₄ _) (h ‹_› ‹_›) ?_ ?_ ?_
      · simpa [*] using h ‹insert a s subseteq _› ‹t subseteq _›
      · simpa [*] using h ‹s subseteq _› ‹insert a t subseteq _›
      · simpa [*] using h ‹insert a s subseteq _› ‹insert a t subseteq _›
    · rw [add_zero, add_mul]
      refine (add_le_add (h ‹_› ‹_›) <| h ‹_› ‹_›).trans ?_
      rw [collapse_of_mem ‹_› (union_mem_sups ‹_› ‹_›) (union_mem_sups ‹_› ‹_›) rfl
        (insert_union _ _ _)]; rw [insert_inter_of_notMem ‹_›]; rw [← mul_add]
      gcongr
      exacts [add_nonneg (h₄ _) <| h₄ _, le_collapse_of_mem ‹_› h₃ rfl <| inter_mem_infs ‹_› ‹_›]
    · rw [zero_add, add_mul]
      refine (add_le_add (h ‹_› ‹_›) <| h ‹_› ‹_›).trans ?_
      rw [collapse_of_mem ‹_› (inter_mem_infs ‹_› ‹_›) (inter_mem_infs ‹_› ‹_›)
        (inter_insert_of_notMem ‹_›) (insert_inter_distrib _ _ _).symm]; rw [union_insert]; rw [insert_union_distrib]; rw [← add_mul]
      gcongr
      exacts [add_nonneg (h₃ _) <| h₃ _,
        le_collapse_of_insert_mem ‹_› h₄ (insert_union_distrib _ _ _).symm (union_mem_sups ‹_› ‹_›)]
    · rw [add_zero, mul_zero]
exact mul_nonneg (collapse_nonneg h₃ _) collapse_nonneg h₄ _
  · rw [add_zero, collapse_eq hat, mul_add]
    split_ifs
    · refine (add_le_add (h ‹_› ‹_›) <| h ‹_› ‹_›).trans ?_
      rw [collapse_of_mem ‹_› (union_mem_sups ‹_› ‹_›) (union_mem_sups ‹_› ‹_›) rfl
        (union_insert _ _ _)]; rw [inter_insert_of_notMem ‹_›]; rw [← mul_add]
      gcongr
      · exact add_nonneg (h₄ _) (h₄ _)
· exact le_collapse_of_mem ‹_› h₃ rfl inter_mem_infs ‹_› ‹_›
    · rw [mul_zero, add_zero]
exact (h ‹_› ‹_›).trans mul_le_mul (le_collapse_of_mem ‹_› h₃ rfl <|
inter_mem_infs ‹_› ‹_›) (le_collapse_of_mem ‹_› h₄ rfl union_mem_sups ‹_› ‹_›)
(h₄ _) collapse_nonneg h₃ _
    · rw [mul_zero, zero_add]
refine (h ‹_› ‹_›).trans mul_le_mul ?_ (le_collapse_of_insert_mem ‹_› h₄
(union_insert _ _ _) union_mem_sups ‹_› ‹_›) (h₄ _) <| collapse_nonneg h₃ _
      exact le_collapse_of_mem (notMem_mono inter_subset_left ‹_›) h₃
(inter_insert_of_notMem ‹_›) inter_mem_infs ‹_› ‹_›
    · simp_rw [mul_zero, add_zero]
exact mul_nonneg (collapse_nonneg h₃ _) collapse_nonneg h₄ _
  · rw [zero_add, collapse_eq hat, mul_add]
    split_ifs
    · refine (add_le_add (h ‹_› ‹_›) <| h ‹_› ‹_›).trans ?_
      rw [collapse_of_mem ‹_› (inter_mem_infs ‹_› ‹_›) (inter_mem_infs ‹_› ‹_›)
        (insert_inter_of_notMem ‹_›) (insert_inter_distrib _ _ _).symm]; rw [insert_inter_of_notMem ‹_›]; rw [← insert_inter_distrib]; rw [insert_union]; rw [insert_union_distrib]; rw [← add_mul]
      gcongr
      · exact add_nonneg (h₃ _) (h₃ _)
      · exact le_collapse_of_insert_mem ‹_› h₄
(insert_union_distrib _ _ _).symm union_mem_sups ‹_› ‹_›
    · rw [mul_zero, add_zero]
refine (h ‹_› ‹_›).trans mul_le_mul (le_collapse_of_mem ‹_› h₃
(insert_inter_of_notMem ‹_›) inter_mem_infs ‹_› ‹_›) (le_collapse_of_insert_mem ‹_› h₄
(insert_union _ _ _) union_mem_sups ‹_› ‹_›) (h₄ _) <| collapse_nonneg h₃ _
    · rw [mul_zero, zero_add]
exact (h ‹_› ‹_›).trans mul_le_mul (le_collapse_of_insert_mem ‹_› h₃
(insert_inter_distrib _ _ _).symm inter_mem_infs ‹_› ‹_›) (le_collapse_of_insert_mem ‹_›
h₄ (insert_union_distrib _ _ _).symm union_mem_sups ‹_› ‹_›) (h₄ _) <|
        collapse_nonneg h₃ _
    · simp_rw [mul_zero, add_zero]
exact mul_nonneg (collapse_nonneg h₃ _) collapse_nonneg h₄ _
  · simp_rw [add_zero, zero_mul]
exact mul_nonneg (collapse_nonneg h₃ _) collapse_nonneg h₄ _

中文:
引理 collapse_modular
  结论: [ExistsAddOfLE β]
  证明: by
  rintro s hsu t htu
  -- Gather a bunch of facts we'll need a lot
have := hsu.trans subset_insert a _
have := htu.trans subset_insert a _
  have := insert_subset_insert a hsu
  have := insert_subset_insert a htu
  have has := notMem_mono hsu hu
  have hat := notMem_mono htu hu
  have : a ∉ s inter t := notMem_mono (inter_subset_left.trans hsu) hu
  have := notMem_union.2 ⟨has, hat⟩
  rw [collapse_eq has]
  split_ifs
  · rw [collapse_eq hat]
    split_ifs
    · rw [collapse_of_mem ‹_› (inter_mem_infs ‹_› ‹_›) (inter_mem_infs ‹_› ‹_›) rfl
        (insert_inter_distrib _ _ _).symm, collapse_of_mem ‹_› (union_mem_sups ‹_› ‹_›)
        (union_mem_sups ‹_› ‹_›) rfl (insert_union_distrib _ _ _).symm]
      refine ineq (h₁ _) (h₁ _) (h₂ _) (h₂ _) (h₃ _) (h₃ _) (h₄ _) (h₄ _) (h ‹_› ‹_›) ?_ ?_ ?_
      · simpa [*] using h ‹insert a s subseteq _› ‹t subseteq _›
      · simpa [*] using h ‹s subseteq _› ‹insert a t subseteq _›
      · simpa [*] using h ‹insert a s subseteq _› ‹insert a t subseteq _›
    · rw [add_zero, add_mul]
      refine (add_le_add (h ‹_› ‹_›) <| h ‹_› ‹_›).trans ?_
      rw [collapse_of_mem ‹_› (union_mem_sups ‹_› ‹_›) (union_mem_sups ‹_› ‹_›) rfl
        (insert_union _ _ _)]; rw [insert_inter_of_notMem ‹_›]; rw [← mul_add]
      gcongr
      exacts [add_nonneg (h₄ _) <| h₄ _, le_collapse_of_mem ‹_› h₃ rfl <| inter_mem_infs ‹_› ‹_›]
    · rw [zero_add, add_mul]
      refine (add_le_add (h ‹_› ‹_›) <| h ‹_› ‹_›).trans ?_
      rw [collapse_of_mem ‹_› (inter_mem_infs ‹_› ‹_›) (inter_mem_infs ‹_› ‹_›)
        (inter_insert_of_notMem ‹_›) (insert_inter_distrib _ _ _).symm]; rw [union_insert]; rw [insert_union_distrib]; rw [← add_mul]
      gcongr
      exacts [add_nonneg (h₃ _) <| h₃ _,
        le_collapse_of_insert_mem ‹_› h₄ (insert_union_distrib _ _ _).symm (union_mem_sups ‹_› ‹_›)]
    · rw [add_zero, mul_zero]
exact mul_nonneg (collapse_nonneg h₃ _) collapse_nonneg h₄ _
  · rw [add_zero, collapse_eq hat, mul_add]
    split_ifs
    · refine (add_le_add (h ‹_› ‹_›) <| h ‹_› ‹_›).trans ?_
      rw [collapse_of_mem ‹_› (union_mem_sups ‹_› ‹_›) (union_mem_sups ‹_› ‹_›) rfl
        (union_insert _ _ _)]; rw [inter_insert_of_notMem ‹_›]; rw [← mul_add]
      gcongr
      · exact add_nonneg (h₄ _) (h₄ _)
· exact le_collapse_of_mem ‹_› h₃ rfl inter_mem_infs ‹_› ‹_›
    · rw [mul_zero, add_zero]
exact (h ‹_› ‹_›).trans mul_le_mul (le_collapse_of_mem ‹_› h₃ rfl <|
inter_mem_infs ‹_› ‹_›) (le_collapse_of_mem ‹_› h₄ rfl union_mem_sups ‹_› ‹_›)
(h₄ _) collapse_nonneg h₃ _
    · rw [mul_zero, zero_add]
refine (h ‹_› ‹_›).trans mul_le_mul ?_ (le_collapse_of_insert_mem ‹_› h₄
(union_insert _ _ _) union_mem_sups ‹_› ‹_›) (h₄ _) <| collapse_nonneg h₃ _
      exact le_collapse_of_mem (notMem_mono inter_subset_left ‹_›) h₃
(inter_insert_of_notMem ‹_›) inter_mem_infs ‹_› ‹_›
    · simp_rw [mul_zero, add_zero]
exact mul_nonneg (collapse_nonneg h₃ _) collapse_nonneg h₄ _
  · rw [zero_add, collapse_eq hat, mul_add]
    split_ifs
    · refine (add_le_add (h ‹_› ‹_›) <| h ‹_› ‹_›).trans ?_
      rw [collapse_of_mem ‹_› (inter_mem_infs ‹_› ‹_›) (inter_mem_infs ‹_› ‹_›)
        (insert_inter_of_notMem ‹_›) (insert_inter_distrib _ _ _).symm]; rw [insert_inter_of_notMem ‹_›]; rw [← insert_inter_distrib]; rw [insert_union]; rw [insert_union_distrib]; rw [← add_mul]
      gcongr
      · exact add_nonneg (h₃ _) (h₃ _)
      · exact le_collapse_of_insert_mem ‹_› h₄
(insert_union_distrib _ _ _).symm union_mem_sups ‹_› ‹_›
    · rw [mul_zero, add_zero]
refine (h ‹_› ‹_›).trans mul_le_mul (le_collapse_of_mem ‹_› h₃
(insert_inter_of_notMem ‹_›) inter_mem_infs ‹_› ‹_›) (le_collapse_of_insert_mem ‹_› h₄
(insert_union _ _ _) union_mem_sups ‹_› ‹_›) (h₄ _) <| collapse_nonneg h₃ _
    · rw [mul_zero, zero_add]
exact (h ‹_› ‹_›).trans mul_le_mul (le_collapse_of_insert_mem ‹_› h₃
(insert_inter_distrib _ _ _).symm inter_mem_infs ‹_› ‹_›) (le_collapse_of_insert_mem ‹_›
h₄ (insert_union_distrib _ _ _).symm union_mem_sups ‹_› ‹_›) (h₄ _) <|
        collapse_nonneg h₃ _
    · simp_rw [mul_zero, add_zero]
exact mul_nonneg (collapse_nonneg h₃ _) collapse_nonneg h₄ _
  · simp_rw [add_zero, zero_mul]
exact mul_nonneg (collapse_nonneg h₃ _) collapse_nonneg h₄ _
-/
lemma collapse_modular [ExistsAddOfLE β]
    (hu : a ∉ u) (h₁ : 0 <= f₁) (h₂ : 0 <= f₂) (h₃ : 0 <= f₃) (h₄ : 0 <= f₄)
    (h : forall ⦃s⦄, s subseteq insert a u -> forall ⦃t⦄, t subseteq insert a u -> f₁ s * f₂ t <= f₃ (s inter t) * f₄ (s union t))
    (𝒜 ℬ : Finset (Finset α)) :
    forall ⦃s⦄, s subseteq u -> forall ⦃t⦄, t subseteq u -> collapse 𝒜 a f₁ s * collapse ℬ a f₂ t <=
      collapse (𝒜 ⊼ ℬ) a f₃ (s inter t) * collapse (𝒜 ⊻ ℬ) a f₄ (s union t) := by
  rintro s hsu t htu
  -- Gather a bunch of facts we'll need a lot
have := hsu.trans subset_insert a _
have := htu.trans subset_insert a _
  have := insert_subset_insert a hsu
  have := insert_subset_insert a htu
  have has := notMem_mono hsu hu
  have hat := notMem_mono htu hu
  have : a ∉ s inter t := notMem_mono (inter_subset_left.trans hsu) hu
  have := notMem_union.2 ⟨has, hat⟩
  rw [collapse_eq has]
  split_ifs
  · rw [collapse_eq hat]
    split_ifs
    · rw [collapse_of_mem ‹_› (inter_mem_infs ‹_› ‹_›) (inter_mem_infs ‹_› ‹_›) rfl
        (insert_inter_distrib _ _ _).symm, collapse_of_mem ‹_› (union_mem_sups ‹_› ‹_›)
        (union_mem_sups ‹_› ‹_›) rfl (insert_union_distrib _ _ _).symm]
      refine ineq (h₁ _) (h₁ _) (h₂ _) (h₂ _) (h₃ _) (h₃ _) (h₄ _) (h₄ _) (h ‹_› ‹_›) ?_ ?_ ?_
      · simpa [*] using h ‹insert a s subseteq _› ‹t subseteq _›
      · simpa [*] using h ‹s subseteq _› ‹insert a t subseteq _›
      · simpa [*] using h ‹insert a s subseteq _› ‹insert a t subseteq _›
    · rw [add_zero, add_mul]
      refine (add_le_add (h ‹_› ‹_›) <| h ‹_› ‹_›).trans ?_
      rw [collapse_of_mem ‹_› (union_mem_sups ‹_› ‹_›) (union_mem_sups ‹_› ‹_›) rfl
        (insert_union _ _ _)]; rw [insert_inter_of_notMem ‹_›]; rw [← mul_add]
      gcongr
      exacts [add_nonneg (h₄ _) <| h₄ _, le_collapse_of_mem ‹_› h₃ rfl <| inter_mem_infs ‹_› ‹_›]
    · rw [zero_add, add_mul]
      refine (add_le_add (h ‹_› ‹_›) <| h ‹_› ‹_›).trans ?_
      rw [collapse_of_mem ‹_› (inter_mem_infs ‹_› ‹_›) (inter_mem_infs ‹_› ‹_›)
        (inter_insert_of_notMem ‹_›) (insert_inter_distrib _ _ _).symm]; rw [union_insert]; rw [insert_union_distrib]; rw [← add_mul]
      gcongr
      exacts [add_nonneg (h₃ _) <| h₃ _,
        le_collapse_of_insert_mem ‹_› h₄ (insert_union_distrib _ _ _).symm (union_mem_sups ‹_› ‹_›)]
    · rw [add_zero, mul_zero]
exact mul_nonneg (collapse_nonneg h₃ _) collapse_nonneg h₄ _
  · rw [add_zero, collapse_eq hat, mul_add]
    split_ifs
    · refine (add_le_add (h ‹_› ‹_›) <| h ‹_› ‹_›).trans ?_
      rw [collapse_of_mem ‹_› (union_mem_sups ‹_› ‹_›) (union_mem_sups ‹_› ‹_›) rfl
        (union_insert _ _ _)]; rw [inter_insert_of_notMem ‹_›]; rw [← mul_add]
      gcongr
      · exact add_nonneg (h₄ _) (h₄ _)
· exact le_collapse_of_mem ‹_› h₃ rfl inter_mem_infs ‹_› ‹_›
    · rw [mul_zero, add_zero]
exact (h ‹_› ‹_›).trans mul_le_mul (le_collapse_of_mem ‹_› h₃ rfl <|
inter_mem_infs ‹_› ‹_›) (le_collapse_of_mem ‹_› h₄ rfl union_mem_sups ‹_› ‹_›)
(h₄ _) collapse_nonneg h₃ _
    · rw [mul_zero, zero_add]
refine (h ‹_› ‹_›).trans mul_le_mul ?_ (le_collapse_of_insert_mem ‹_› h₄
(union_insert _ _ _) union_mem_sups ‹_› ‹_›) (h₄ _) <| collapse_nonneg h₃ _
      exact le_collapse_of_mem (notMem_mono inter_subset_left ‹_›) h₃
(inter_insert_of_notMem ‹_›) inter_mem_infs ‹_› ‹_›
    · simp_rw [mul_zero, add_zero]
exact mul_nonneg (collapse_nonneg h₃ _) collapse_nonneg h₄ _
  · rw [zero_add, collapse_eq hat, mul_add]
    split_ifs
    · refine (add_le_add (h ‹_› ‹_›) <| h ‹_› ‹_›).trans ?_
      rw [collapse_of_mem ‹_› (inter_mem_infs ‹_› ‹_›) (inter_mem_infs ‹_› ‹_›)
        (insert_inter_of_notMem ‹_›) (insert_inter_distrib _ _ _).symm]; rw [insert_inter_of_notMem ‹_›]; rw [← insert_inter_distrib]; rw [insert_union]; rw [insert_union_distrib]; rw [← add_mul]
      gcongr
      · exact add_nonneg (h₃ _) (h₃ _)
      · exact le_collapse_of_insert_mem ‹_› h₄
(insert_union_distrib _ _ _).symm union_mem_sups ‹_› ‹_›
    · rw [mul_zero, add_zero]
refine (h ‹_› ‹_›).trans mul_le_mul (le_collapse_of_mem ‹_› h₃
(insert_inter_of_notMem ‹_›) inter_mem_infs ‹_› ‹_›) (le_collapse_of_insert_mem ‹_› h₄
(insert_union _ _ _) union_mem_sups ‹_› ‹_›) (h₄ _) <| collapse_nonneg h₃ _
    · rw [mul_zero, zero_add]
exact (h ‹_› ‹_›).trans mul_le_mul (le_collapse_of_insert_mem ‹_› h₃
(insert_inter_distrib _ _ _).symm inter_mem_infs ‹_› ‹_›) (le_collapse_of_insert_mem ‹_›
h₄ (insert_union_distrib _ _ _).symm union_mem_sups ‹_› ‹_›) (h₄ _) <|
        collapse_nonneg h₃ _
    · simp_rw [mul_zero, add_zero]
exact mul_nonneg (collapse_nonneg h₃ _) collapse_nonneg h₄ _
  · simp_rw [add_zero, zero_mul]
exact mul_nonneg (collapse_nonneg h₃ _) collapse_nonneg h₄ _

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
omit [LinearOrder β] [IsStrictOrderedRing β] in
/--
lemma `sum_collapse` / 引理 `sum_collapse`

English:
lemma sum_collapse
  given: (h𝒜 : 𝒜 subseteq (insert a u).powerset) (hu : a ∉ u)
  proof: by
  calc
    _ = ∑ s in u.powerset inter 𝒜, f s + ∑ s in u.powerset.image (insert a) inter 𝒜, f s := ?_
    _ = ∑ s in u.powerset inter 𝒜, f s + ∑ s in ((insert a u).powerset \ u.powerset) inter 𝒜, f s := ?_
    _ = ∑ s in 𝒜, f s := ?_
  · rw [← Finset.sum_ite_mem, ← Finset.sum_ite_mem, sum_image, ← sum_add_distrib]
    · exact sum_congr rfl fun s hs => collapse_eq (notMem_mono (mem_powerset.1 hs) hu) _ _
    · exact (insert_erase_invOn.2.injOn).mono fun s hs => notMem_mono (mem_powerset.1 hs) hu
  · congr with s
    simp only [mem_image, mem_powerset, mem_sdiff, subset_insert_iff]
    refine ⟨?_, fun h => ⟨_, h.1, ?_⟩⟩
    · rintro ⟨s, hs, rfl⟩
exact ⟨subset_insert_iff.1 insert_subset_insert _ hs, fun h =>
hu h mem_insert_self _ _⟩
    · rw [insert_erase (erase_ne_self.1 fun hs => ?_)]
      rw [hs] at h
      exact h.2 h.1
  · rw [← sum_union (disjoint_sdiff_self_right.mono inf_le_left inf_le_left),
      ← union_inter_distrib_right, union_sdiff_of_subset (powerset_mono.2 <| subset_insert _ _),
      inter_eq_right.2 h𝒜]

中文:
引理 sum_collapse
  条件: (h𝒜 : 𝒜 subseteq (insert a u).powerset) (hu : a ∉ u)
  证明: by
  calc
    _ = ∑ s in u.powerset inter 𝒜, f s + ∑ s in u.powerset.image (insert a) inter 𝒜, f s := ?_
    _ = ∑ s in u.powerset inter 𝒜, f s + ∑ s in ((insert a u).powerset \ u.powerset) inter 𝒜, f s := ?_
    _ = ∑ s in 𝒜, f s := ?_
  · rw [← Finset.sum_ite_mem, ← Finset.sum_ite_mem, sum_image, ← sum_add_distrib]
    · exact sum_congr rfl fun s hs => collapse_eq (notMem_mono (mem_powerset.1 hs) hu) _ _
    · exact (insert_erase_invOn.2.injOn).mono fun s hs => notMem_mono (mem_powerset.1 hs) hu
  · congr with s
    simp only [mem_image, mem_powerset, mem_sdiff, subset_insert_iff]
    refine ⟨?_, fun h => ⟨_, h.1, ?_⟩⟩
    · rintro ⟨s, hs, rfl⟩
exact ⟨subset_insert_iff.1 insert_subset_insert _ hs, fun h =>
hu h mem_insert_self _ _⟩
    · rw [insert_erase (erase_ne_self.1 fun hs => ?_)]
      rw [hs] at h
      exact h.2 h.1
  · rw [← sum_union (disjoint_sdiff_self_right.mono inf_le_left inf_le_left),
      ← union_inter_distrib_right, union_sdiff_of_subset (powerset_mono.2 <| subset_insert _ _),
      inter_eq_right.2 h𝒜]

Depends on / 依赖: Finset, Finset.sum_ite_mem, collapse_eq, insert, insert_erase_invOn, mem_powerset, notMem_mono, powerset, sum_add_distrib, sum_congr, sum_image, sum_ite_mem, u.powerset, u.powerset.image
-/
lemma sum_collapse (h𝒜 : 𝒜 subseteq (insert a u).powerset) (hu : a ∉ u) :
    ∑ s in u.powerset, collapse 𝒜 a f s = ∑ s in 𝒜, f s := by
  calc
    _ = ∑ s in u.powerset inter 𝒜, f s + ∑ s in u.powerset.image (insert a) inter 𝒜, f s := ?_
    _ = ∑ s in u.powerset inter 𝒜, f s + ∑ s in ((insert a u).powerset \ u.powerset) inter 𝒜, f s := ?_
    _ = ∑ s in 𝒜, f s := ?_
  · rw [← Finset.sum_ite_mem, ← Finset.sum_ite_mem, sum_image, ← sum_add_distrib]
    · exact sum_congr rfl fun s hs => collapse_eq (notMem_mono (mem_powerset.1 hs) hu) _ _
    · exact (insert_erase_invOn.2.injOn).mono fun s hs => notMem_mono (mem_powerset.1 hs) hu
  · congr with s
    simp only [mem_image, mem_powerset, mem_sdiff, subset_insert_iff]
    refine ⟨?_, fun h => ⟨_, h.1, ?_⟩⟩
    · rintro ⟨s, hs, rfl⟩
exact ⟨subset_insert_iff.1 insert_subset_insert _ hs, fun h =>
hu h mem_insert_self _ _⟩
    · rw [insert_erase (erase_ne_self.1 fun hs => ?_)]
      rw [hs] at h
      exact h.2 h.1
  · rw [← sum_union (disjoint_sdiff_self_right.mono inf_le_left inf_le_left),
      ← union_inter_distrib_right, union_sdiff_of_subset (powerset_mono.2 <| subset_insert _ _),
      inter_eq_right.2 h𝒜]

variable [ExistsAddOfLE β]

/--
lemma `Finset.four_functions_theorem` / 引理 `Finset.four_functions_theorem`

English:
lemma Finset.four_functions_theorem
  statement: (u : Finset α)
  proof: by
  induction u using Finset.induction generalizing f₁ f₂ f₃ f₄ 𝒜 ℬ with
  | empty =>
    simp only [Finset.powerset_empty, Finset.subset_singleton_iff] at h𝒜 hℬ
    obtain rfl | rfl := h𝒜
    · simp
    obtain rfl | rfl := hℬ
    · simp
    simpa using h (subset_refl ∅) subset_rfl
  | insert a u hu ih =>
    specialize ih (collapse_nonneg h₁) (collapse_nonneg h₂) (collapse_nonneg h₃)
      (collapse_nonneg h₄) (collapse_modular hu h₁ h₂ h₃ h₄ h 𝒜 ℬ) Subset.rfl Subset.rfl
    have : 𝒜 ⊼ ℬ subseteq powerset (insert a u) := by simpa using infs_subset h𝒜 hℬ
    have : 𝒜 ⊻ ℬ subseteq powerset (insert a u) := by simpa using sups_subset h𝒜 hℬ
    simpa only [powerset_sups_powerset_self, powerset_infs_powerset_self, sum_collapse,
      not_false_eq_true, *] using ih

中文:
引理 有限集.four_functions_theorem
  结论: (u : 有限集 α)
  证明: by
  induction u using Finset.induction generalizing f₁ f₂ f₃ f₄ 𝒜 ℬ with
  | empty =>
    simp only [Finset.powerset_empty, Finset.subset_singleton_iff] at h𝒜 hℬ
    obtain rfl | rfl := h𝒜
    · simp
    obtain rfl | rfl := hℬ
    · simp
    simpa using h (subset_refl ∅) subset_rfl
  | insert a u hu ih =>
    specialize ih (collapse_nonneg h₁) (collapse_nonneg h₂) (collapse_nonneg h₃)
      (collapse_nonneg h₄) (collapse_modular hu h₁ h₂ h₃ h₄ h 𝒜 ℬ) Subset.rfl Subset.rfl
    have : 𝒜 ⊼ ℬ subseteq powerset (insert a u) := by simpa using infs_subset h𝒜 hℬ
    have : 𝒜 ⊻ ℬ subseteq powerset (insert a u) := by simpa using sups_subset h𝒜 hℬ
    simpa only [powerset_sups_powerset_self, powerset_infs_powerset_self, sum_collapse,
      not_false_eq_true, *] using ih
-/
protected lemma Finset.four_functions_theorem (u : Finset α)
    (h₁ : 0 <= f₁) (h₂ : 0 <= f₂) (h₃ : 0 <= f₃) (h₄ : 0 <= f₄)
    (h : forall ⦃s⦄, s subseteq u -> forall ⦃t⦄, t subseteq u -> f₁ s * f₂ t <= f₃ (s inter t) * f₄ (s union t))
    {𝒜 ℬ : Finset (Finset α)} (h𝒜 : 𝒜 subseteq u.powerset) (hℬ : ℬ subseteq u.powerset) :
    (∑ s in 𝒜, f₁ s) * ∑ s in ℬ, f₂ s <= (∑ s in 𝒜 ⊼ ℬ, f₃ s) * ∑ s in 𝒜 ⊻ ℬ, f₄ s := by
  induction u using Finset.induction generalizing f₁ f₂ f₃ f₄ 𝒜 ℬ with
  | empty =>
    simp only [Finset.powerset_empty, Finset.subset_singleton_iff] at h𝒜 hℬ
    obtain rfl | rfl := h𝒜
    · simp
    obtain rfl | rfl := hℬ
    · simp
    simpa using h (subset_refl ∅) subset_rfl
  | insert a u hu ih =>
    specialize ih (collapse_nonneg h₁) (collapse_nonneg h₂) (collapse_nonneg h₃)
      (collapse_nonneg h₄) (collapse_modular hu h₁ h₂ h₃ h₄ h 𝒜 ℬ) Subset.rfl Subset.rfl
    have : 𝒜 ⊼ ℬ subseteq powerset (insert a u) := by simpa using infs_subset h𝒜 hℬ
    have : 𝒜 ⊻ ℬ subseteq powerset (insert a u) := by simpa using sups_subset h𝒜 hℬ
    simpa only [powerset_sups_powerset_self, powerset_infs_powerset_self, sum_collapse,
      not_false_eq_true, *] using ih

variable (f₁ f₂ f₃ f₄) [Finite α]

/--
lemma `four_functions_theorem_aux` / 引理 `four_functions_theorem_aux`

English:
lemma four_functions_theorem_aux
  statement: (h₁ : 0 <= f₁) (h₂ : 0 <= f₂) (h₃ : 0 <= f₃) (h₄ : 0 <= f₄)
  proof: by
  have := Fintype.ofFinite α
  refine univ.four_functions_theorem h₁ h₂ h₃ h₄ ?_ ?_ ?_ <;> simp [h]

中文:
引理 four_functions_theorem_aux
  结论: (h₁ : 0 <= f₁) (h₂ : 0 <= f₂) (h₃ : 0 <= f₃) (h₄ : 0 <= f₄)
  证明: by
  have := Fintype.ofFinite α
  refine univ.four_functions_theorem h₁ h₂ h₃ h₄ ?_ ?_ ?_ <;> simp [h]
-/
private lemma four_functions_theorem_aux (h₁ : 0 <= f₁) (h₂ : 0 <= f₂) (h₃ : 0 <= f₃) (h₄ : 0 <= f₄)
    (h : forall s t, f₁ s * f₂ t <= f₃ (s inter t) * f₄ (s union t)) (𝒜 ℬ : Finset (Finset α)) :
    (∑ s in 𝒜, f₁ s) * ∑ s in ℬ, f₂ s <= (∑ s in 𝒜 ⊼ ℬ, f₃ s) * ∑ s in 𝒜 ⊻ ℬ, f₄ s := by
  have := Fintype.ofFinite α
  refine univ.four_functions_theorem h₁ h₂ h₃ h₄ ?_ ?_ ?_ <;> simp [h]

end Finset

section DistribLattice
variable [DistribLattice α] [CommSemiring β] [LinearOrder β] [IsStrictOrderedRing β]
  [ExistsAddOfLE β] (f f₁ f₂ f₃ f₄ g μ : α -> β)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `four_functions_theorem` / 引理 `four_functions_theorem`

English:
lemma four_functions_theorem
  statement: [DecidableEq α] (h₁ : 0 <= f₁) (h₂ : 0 <= f₂) (h₃ : 0 <= f₃) (h₄ : 0 <= f₄)
  proof: by
  classical
  set L : Sublattice α := ⟨latticeClosure (s union t), isSublattice_latticeClosure.1,
    isSublattice_latticeClosure.2⟩
  have : Finite L := (s.finite_toSet.union t.finite_toSet).latticeClosure.to_subtype
  set s' : Finset L := s.preimage (↑) Subtype.coe_injective.injOn
  set t' : Finset L := t.preimage (↑) Subtype.coe_injective.injOn
  have hs' : s'.map ⟨L.subtype, Subtype.coe_injective⟩ = s := by
    simpa [s', map_eq_image, image_preimage, filter_eq_self] using!
fun a ha => subset_latticeClosure Set.subset_union_left ha
  have ht' : t'.map ⟨L.subtype, Subtype.coe_injective⟩ = t := by
    simpa [t', map_eq_image, image_preimage, filter_eq_self] using!
fun a ha => subset_latticeClosure Set.subset_union_right ha
  clear_value s' t'
  obtain ⟨β, _, _, g, hg⟩ := exists_birkhoff_representation L
  have := four_functions_theorem_aux (extend g (f₁ ∘ (↑)) 0) (extend g (f₂ ∘ (↑)) 0)
    (extend g (f₃ ∘ (↑)) 0) (extend g (f₄ ∘ (↑)) 0) (extend_nonneg (fun _ => h₁ _) le_rfl)
    (extend_nonneg (fun _ => h₂ _) le_rfl) (extend_nonneg (fun _ => h₃ _) le_rfl)
    (extend_nonneg (fun _ => h₄ _) le_rfl) ?_ (s'.map ⟨g, hg⟩) (t'.map ⟨g, hg⟩)
  · simpa only [← hs', ← ht', ← map_sups, ← map_infs, sum_map, Embedding.coeFn_mk, hg.extend_apply]
      using! this
  rintro s t
  obtain ⟨a, rfl⟩ | hs := em (exists a, g a = s)
  · obtain ⟨b, rfl⟩ | ht := em (exists b, g b = t)
    · simp_rw [← sup_eq_union, ← inf_eq_inter, ← map_sup, ← map_inf, hg.extend_apply]
      exact h _ _
    · simpa [extend_apply' _ _ _ ht] using! mul_nonneg
        (extend_nonneg (fun a : L => h₃ a) le_rfl _) (extend_nonneg (fun a : L => h₄ a) le_rfl _)
  · simpa [extend_apply' _ _ _ hs] using! mul_nonneg
      (extend_nonneg (fun a : L => h₃ a) le_rfl _) (extend_nonneg (fun a : L => h₄ a) le_rfl _)

中文:
引理 four_functions_theorem
  结论: [DecidableEq α] (h₁ : 0 <= f₁) (h₂ : 0 <= f₂) (h₃ : 0 <= f₃) (h₄ : 0 <= f₄)
  证明: by
  classical
  set L : Sublattice α := ⟨latticeClosure (s union t), isSublattice_latticeClosure.1,
    isSublattice_latticeClosure.2⟩
  have : Finite L := (s.finite_toSet.union t.finite_toSet).latticeClosure.to_subtype
  set s' : Finset L := s.preimage (↑) Subtype.coe_injective.injOn
  set t' : Finset L := t.preimage (↑) Subtype.coe_injective.injOn
  have hs' : s'.map ⟨L.subtype, Subtype.coe_injective⟩ = s := by
    simpa [s', map_eq_image, image_preimage, filter_eq_self] using!
fun a ha => subset_latticeClosure Set.subset_union_left ha
  have ht' : t'.map ⟨L.subtype, Subtype.coe_injective⟩ = t := by
    simpa [t', map_eq_image, image_preimage, filter_eq_self] using!
fun a ha => subset_latticeClosure Set.subset_union_right ha
  clear_value s' t'
  obtain ⟨β, _, _, g, hg⟩ := exists_birkhoff_representation L
  have := four_functions_theorem_aux (extend g (f₁ ∘ (↑)) 0) (extend g (f₂ ∘ (↑)) 0)
    (extend g (f₃ ∘ (↑)) 0) (extend g (f₄ ∘ (↑)) 0) (extend_nonneg (fun _ => h₁ _) le_rfl)
    (extend_nonneg (fun _ => h₂ _) le_rfl) (extend_nonneg (fun _ => h₃ _) le_rfl)
    (extend_nonneg (fun _ => h₄ _) le_rfl) ?_ (s'.map ⟨g, hg⟩) (t'.map ⟨g, hg⟩)
  · simpa only [← hs', ← ht', ← map_sups, ← map_infs, sum_map, Embedding.coeFn_mk, hg.extend_apply]
      using! this
  rintro s t
  obtain ⟨a, rfl⟩ | hs := em (exists a, g a = s)
  · obtain ⟨b, rfl⟩ | ht := em (exists b, g b = t)
    · simp_rw [← sup_eq_union, ← inf_eq_inter, ← map_sup, ← map_inf, hg.extend_apply]
      exact h _ _
    · simpa [extend_apply' _ _ _ ht] using! mul_nonneg
        (extend_nonneg (fun a : L => h₃ a) le_rfl _) (extend_nonneg (fun a : L => h₄ a) le_rfl _)
  · simpa [extend_apply' _ _ _ hs] using! mul_nonneg
      (extend_nonneg (fun a : L => h₃ a) le_rfl _) (extend_nonneg (fun a : L => h₄ a) le_rfl _)

Depends on / 依赖: Finite, Finset, L.subtype, Sublattice, Subtype, Subtype.coe_injective, Subtype.coe_injective.injOn, classical, coe_injective, filter_eq_self, finite_toSet, image_preimage, isSublattice_latticeClosure, latticeClosure, latticeClosure.to_subtype, map_eq_image, preimage, s.finite_toSet.union, s.preimage, subset_latticeClosure
-/
lemma four_functions_theorem [DecidableEq α] (h₁ : 0 <= f₁) (h₂ : 0 <= f₂) (h₃ : 0 <= f₃) (h₄ : 0 <= f₄)
    (h : forall a b, f₁ a * f₂ b <= f₃ (a ⊓ b) * f₄ (a ⊔ b)) (s t : Finset α) :
    (∑ a in s, f₁ a) * ∑ a in t, f₂ a <= (∑ a in s ⊼ t, f₃ a) * ∑ a in s ⊻ t, f₄ a := by
  classical
  set L : Sublattice α := ⟨latticeClosure (s union t), isSublattice_latticeClosure.1,
    isSublattice_latticeClosure.2⟩
  have : Finite L := (s.finite_toSet.union t.finite_toSet).latticeClosure.to_subtype
  set s' : Finset L := s.preimage (↑) Subtype.coe_injective.injOn
  set t' : Finset L := t.preimage (↑) Subtype.coe_injective.injOn
  have hs' : s'.map ⟨L.subtype, Subtype.coe_injective⟩ = s := by
    simpa [s', map_eq_image, image_preimage, filter_eq_self] using!
fun a ha => subset_latticeClosure Set.subset_union_left ha
  have ht' : t'.map ⟨L.subtype, Subtype.coe_injective⟩ = t := by
    simpa [t', map_eq_image, image_preimage, filter_eq_self] using!
fun a ha => subset_latticeClosure Set.subset_union_right ha
  clear_value s' t'
  obtain ⟨β, _, _, g, hg⟩ := exists_birkhoff_representation L
  have := four_functions_theorem_aux (extend g (f₁ ∘ (↑)) 0) (extend g (f₂ ∘ (↑)) 0)
    (extend g (f₃ ∘ (↑)) 0) (extend g (f₄ ∘ (↑)) 0) (extend_nonneg (fun _ => h₁ _) le_rfl)
    (extend_nonneg (fun _ => h₂ _) le_rfl) (extend_nonneg (fun _ => h₃ _) le_rfl)
    (extend_nonneg (fun _ => h₄ _) le_rfl) ?_ (s'.map ⟨g, hg⟩) (t'.map ⟨g, hg⟩)
  · simpa only [← hs', ← ht', ← map_sups, ← map_infs, sum_map, Embedding.coeFn_mk, hg.extend_apply]
      using! this
  rintro s t
  obtain ⟨a, rfl⟩ | hs := em (exists a, g a = s)
  · obtain ⟨b, rfl⟩ | ht := em (exists b, g b = t)
    · simp_rw [← sup_eq_union, ← inf_eq_inter, ← map_sup, ← map_inf, hg.extend_apply]
      exact h _ _
    · simpa [extend_apply' _ _ _ ht] using! mul_nonneg
        (extend_nonneg (fun a : L => h₃ a) le_rfl _) (extend_nonneg (fun a : L => h₄ a) le_rfl _)
  · simpa [extend_apply' _ _ _ hs] using! mul_nonneg
      (extend_nonneg (fun a : L => h₃ a) le_rfl _) (extend_nonneg (fun a : L => h₄ a) le_rfl _)

/--
lemma `Finset.le_card_infs_mul_card_sups` / 引理 `Finset.le_card_infs_mul_card_sups`

English:
lemma Finset.le_card_infs_mul_card_sups
  given: [DecidableEq α] (s t : Finset α)
  proof: by
  simpa using four_functions_theorem (1 : α -> Nat) 1 1 1 zero_le_one zero_le_one zero_le_one
    zero_le_one (fun _ _ => le_rfl) s t

中文:
引理 有限集.le_card_infs_mul_card_sups
  条件: [DecidableEq α] (s t : 有限集 α)
  证明: by
  simpa using four_functions_theorem (1 : α -> Nat) 1 1 1 zero_le_one zero_le_one zero_le_one
    zero_le_one (fun _ _ => le_rfl) s t

Depends on / 依赖: four_functions_theorem, le_rfl, zero_le_one
-/
lemma Finset.le_card_infs_mul_card_sups [DecidableEq α] (s t : Finset α) :
    #s * #t <= #(s ⊼ t) * #(s ⊻ t) := by
  simpa using four_functions_theorem (1 : α -> Nat) 1 1 1 zero_le_one zero_le_one zero_le_one
    zero_le_one (fun _ _ => le_rfl) s t

variable [Fintype α]

/--
lemma `four_functions_theorem_univ` / 引理 `four_functions_theorem_univ`

English:
lemma four_functions_theorem_univ
  statement: (h₁ : 0 <= f₁) (h₂ : 0 <= f₂) (h₃ : 0 <= f₃) (h₄ : 0 <= f₄)
  proof: by
  classical simpa using four_functions_theorem f₁ f₂ f₃ f₄ h₁ h₂ h₃ h₄ h univ univ

中文:
引理 four_functions_theorem_univ
  结论: (h₁ : 0 <= f₁) (h₂ : 0 <= f₂) (h₃ : 0 <= f₃) (h₄ : 0 <= f₄)
  证明: by
  classical simpa using four_functions_theorem f₁ f₂ f₃ f₄ h₁ h₂ h₃ h₄ h univ univ

Depends on / 依赖: classical, four_functions_theorem
-/
lemma four_functions_theorem_univ (h₁ : 0 <= f₁) (h₂ : 0 <= f₂) (h₃ : 0 <= f₃) (h₄ : 0 <= f₄)
    (h : forall a b, f₁ a * f₂ b <= f₃ (a ⊓ b) * f₄ (a ⊔ b)) :
    (∑ a, f₁ a) * ∑ a, f₂ a <= (∑ a, f₃ a) * ∑ a, f₄ a := by
  classical simpa using four_functions_theorem f₁ f₂ f₃ f₄ h₁ h₂ h₃ h₄ h univ univ

/--
lemma `holley` / 引理 `holley`

English:
lemma holley
  statement: (hμ₀ : 0 <= μ) (hf : 0 <= f) (hg : 0 <= g) (hμ : Monotone μ)
  proof: by
  classical
  obtain rfl | hf := hf.eq_or_lt
  · simp only [Pi.zero_apply, sum_const_zero, eq_comm, Fintype.sum_eq_zero_iff_of_nonneg hg] at hfg
    simp [hfg]
  obtain rfl | hg := hg.eq_or_lt
  · simp only [Pi.zero_apply, sum_const_zero, Fintype.sum_eq_zero_iff_of_nonneg hf.le] at hfg
    simp [hfg]
  have := four_functions_theorem g (μ * f) f (μ * g) hg.le (mul_nonneg hμ₀ hf.le) hf.le
    (mul_nonneg hμ₀ hg.le) (fun a b => ?_) univ univ
  · simpa [hfg, sum_pos hg] using this
  · simp_rw [Pi.mul_apply, mul_left_comm _ (μ _), mul_comm (g _)]
    rw [sup_comm]; rw [inf_comm]
exact mul_le_mul (hμ le_sup_left) (h _ _) (mul_nonneg (hf.le _) <| hg.le _) hμ₀ _

中文:
引理 holley
  结论: (hμ₀ : 0 <= μ) (hf : 0 <= f) (hg : 0 <= g) (hμ : 递增 μ)
  证明: by
  classical
  obtain rfl | hf := hf.eq_or_lt
  · simp only [Pi.zero_apply, sum_const_zero, eq_comm, Fintype.sum_eq_zero_iff_of_nonneg hg] at hfg
    simp [hfg]
  obtain rfl | hg := hg.eq_or_lt
  · simp only [Pi.zero_apply, sum_const_zero, Fintype.sum_eq_zero_iff_of_nonneg hf.le] at hfg
    simp [hfg]
  have := four_functions_theorem g (μ * f) f (μ * g) hg.le (mul_nonneg hμ₀ hf.le) hf.le
    (mul_nonneg hμ₀ hg.le) (fun a b => ?_) univ univ
  · simpa [hfg, sum_pos hg] using this
  · simp_rw [Pi.mul_apply, mul_left_comm _ (μ _), mul_comm (g _)]
    rw [sup_comm]; rw [inf_comm]
exact mul_le_mul (hμ le_sup_left) (h _ _) (mul_nonneg (hf.le _) <| hg.le _) hμ₀ _

Depends on / 依赖: Fintype, Fintype.sum_eq_zero_iff_of_nonneg, Pi.mul_apply, Pi.zero_apply, classical, eq_comm, eq_or_lt, four_functions_theorem, hf.eq_or_lt, hf.le, hg.eq_or_lt, hg.le, mul_apply, mul_left_comm, mul_nonneg, simp_rw, sum_const_zero, sum_eq_zero_iff_of_nonneg, sum_pos, zero_apply
-/
lemma holley (hμ₀ : 0 <= μ) (hf : 0 <= f) (hg : 0 <= g) (hμ : Monotone μ)
    (hfg : ∑ a, f a = ∑ a, g a) (h : forall a b, f a * g b <= f (a ⊓ b) * g (a ⊔ b)) :
    ∑ a, μ a * f a <= ∑ a, μ a * g a := by
  classical
  obtain rfl | hf := hf.eq_or_lt
  · simp only [Pi.zero_apply, sum_const_zero, eq_comm, Fintype.sum_eq_zero_iff_of_nonneg hg] at hfg
    simp [hfg]
  obtain rfl | hg := hg.eq_or_lt
  · simp only [Pi.zero_apply, sum_const_zero, Fintype.sum_eq_zero_iff_of_nonneg hf.le] at hfg
    simp [hfg]
  have := four_functions_theorem g (μ * f) f (μ * g) hg.le (mul_nonneg hμ₀ hf.le) hf.le
    (mul_nonneg hμ₀ hg.le) (fun a b => ?_) univ univ
  · simpa [hfg, sum_pos hg] using this
  · simp_rw [Pi.mul_apply, mul_left_comm _ (μ _), mul_comm (g _)]
    rw [sup_comm]; rw [inf_comm]
exact mul_le_mul (hμ le_sup_left) (h _ _) (mul_nonneg (hf.le _) <| hg.le _) hμ₀ _

/--
lemma `fkg` / 引理 `fkg`

English:
lemma fkg
  statement: (hμ₀ : 0 <= μ) (hf₀ : 0 <= f) (hg₀ : 0 <= g) (hf : Monotone f) (hg : Monotone g)
  proof: by
  refine four_functions_theorem_univ (μ * f) (μ * g) μ _ (mul_nonneg hμ₀ hf₀) (mul_nonneg hμ₀ hg₀)
    hμ₀ (mul_nonneg hμ₀ <| mul_nonneg hf₀ hg₀) (fun a b => ?_)
  dsimp
  rw [mul_mul_mul_comm]; rw [← mul_assoc (μ (a ⊓ b))]
  exact mul_le_mul (hμ _ _) (mul_le_mul (hf le_sup_left) (hg le_sup_right) (hg₀ _) <| hf₀ _)
(mul_nonneg (hf₀ _) <| hg₀ _) mul_nonneg (hμ₀ _) hμ₀ _

中文:
引理 fkg
  结论: (hμ₀ : 0 <= μ) (hf₀ : 0 <= f) (hg₀ : 0 <= g) (hf : 递增 f) (hg : 递增 g)
  证明: by
  refine four_functions_theorem_univ (μ * f) (μ * g) μ _ (mul_nonneg hμ₀ hf₀) (mul_nonneg hμ₀ hg₀)
    hμ₀ (mul_nonneg hμ₀ <| mul_nonneg hf₀ hg₀) (fun a b => ?_)
  dsimp
  rw [mul_mul_mul_comm]; rw [← mul_assoc (μ (a ⊓ b))]
  exact mul_le_mul (hμ _ _) (mul_le_mul (hf le_sup_left) (hg le_sup_right) (hg₀ _) <| hf₀ _)
(mul_nonneg (hf₀ _) <| hg₀ _) mul_nonneg (hμ₀ _) hμ₀ _

Depends on / 依赖: four_functions_theorem_univ, le_sup_left, le_sup_right, mul_assoc, mul_le_mul, mul_mul_mul_comm, mul_nonneg
-/
lemma fkg (hμ₀ : 0 <= μ) (hf₀ : 0 <= f) (hg₀ : 0 <= g) (hf : Monotone f) (hg : Monotone g)
    (hμ : forall a b, μ a * μ b <= μ (a ⊓ b) * μ (a ⊔ b)) :
    (∑ a, μ a * f a) * ∑ a, μ a * g a <= (∑ a, μ a) * ∑ a, μ a * (f a * g a) := by
  refine four_functions_theorem_univ (μ * f) (μ * g) μ _ (mul_nonneg hμ₀ hf₀) (mul_nonneg hμ₀ hg₀)
    hμ₀ (mul_nonneg hμ₀ <| mul_nonneg hf₀ hg₀) (fun a b => ?_)
  dsimp
  rw [mul_mul_mul_comm]; rw [← mul_assoc (μ (a ⊓ b))]
  exact mul_le_mul (hμ _ _) (mul_le_mul (hf le_sup_left) (hg le_sup_right) (hg₀ _) <| hf₀ _)
(mul_nonneg (hf₀ _) <| hg₀ _) mul_nonneg (hμ₀ _) hμ₀ _

end DistribLattice

open Booleanisation

variable [DecidableEq α] [GeneralizedBooleanAlgebra α]

/--
lemma `Finset.le_card_diffs_mul_card_diffs` / 引理 `Finset.le_card_diffs_mul_card_diffs`

English:
lemma Finset.le_card_diffs_mul_card_diffs
  given: (s t : Finset α)
  proof: by
  have : forall s t : Finset α, (s \\ t).map ⟨_, liftLatticeHom_injective⟩ =
      s.map ⟨_, liftLatticeHom_injective⟩ \\ t.map ⟨_, liftLatticeHom_injective⟩ := by
    rintro s t
    simp_rw [map_eq_image]
    exact image_image₂_distrib fun a b => rfl
  simpa [← card_compls (_ ⊻ _), ← map_sup, ← map_inf, ← this] using
    (s.map ⟨_, liftLatticeHom_injective⟩).le_card_infs_mul_card_sups
      (t.map ⟨_, liftLatticeHom_injective⟩)ᶜˢ

中文:
引理 有限集.le_card_diffs_mul_card_diffs
  条件: (s t : 有限集 α)
  证明: by
  have : forall s t : Finset α, (s \\ t).map ⟨_, liftLatticeHom_injective⟩ =
      s.map ⟨_, liftLatticeHom_injective⟩ \\ t.map ⟨_, liftLatticeHom_injective⟩ := by
    rintro s t
    simp_rw [map_eq_image]
    exact image_image₂_distrib fun a b => rfl
  simpa [← card_compls (_ ⊻ _), ← map_sup, ← map_inf, ← this] using
    (s.map ⟨_, liftLatticeHom_injective⟩).le_card_infs_mul_card_sups
      (t.map ⟨_, liftLatticeHom_injective⟩)ᶜˢ

Depends on / 依赖: Finset, card_compls, le_card_infs_mul_card_sups, liftLatticeHom_injective, map_eq_image, map_inf, map_sup, s.map, simp_rw, t.map
-/
lemma Finset.le_card_diffs_mul_card_diffs (s t : Finset α) :
    #s * #t <= #(s \\ t) * #(t \\ s) := by
  have : forall s t : Finset α, (s \\ t).map ⟨_, liftLatticeHom_injective⟩ =
      s.map ⟨_, liftLatticeHom_injective⟩ \\ t.map ⟨_, liftLatticeHom_injective⟩ := by
    rintro s t
    simp_rw [map_eq_image]
    exact image_image₂_distrib fun a b => rfl
  simpa [← card_compls (_ ⊻ _), ← map_sup, ← map_inf, ← this] using
    (s.map ⟨_, liftLatticeHom_injective⟩).le_card_infs_mul_card_sups
      (t.map ⟨_, liftLatticeHom_injective⟩)ᶜˢ

/--
lemma `Finset.card_le_card_diffs` / 引理 `Finset.card_le_card_diffs`

English:
lemma Finset.card_le_card_diffs
  given: (s : Finset α)
  statement: #s <= #(s \\ s)
  proof: le_of_pow_le_pow_left₀ two_ne_zero zero_le by
    simpa [← sq] using s.le_card_diffs_mul_card_diffs s

中文:
引理 有限集.card_le_card_diffs
  条件: (s : 有限集 α)
  结论: #s <= #(s \\ s)
  证明: le_of_pow_le_pow_left₀ two_ne_zero zero_le by
    simpa [← sq] using s.le_card_diffs_mul_card_diffs s

Depends on / 依赖: le_card_diffs_mul_card_diffs, s.le_card_diffs_mul_card_diffs, two_ne_zero, zero_le
-/
lemma Finset.card_le_card_diffs (s : Finset α) : #s <= #(s \\ s) :=
le_of_pow_le_pow_left₀ two_ne_zero zero_le by
    simpa [← sq] using s.le_card_diffs_mul_card_diffs s
