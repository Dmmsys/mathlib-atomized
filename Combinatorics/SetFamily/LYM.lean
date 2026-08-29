/-
Copyright (c) 2022 Bhavik Mehta, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov, Yaël Dillies
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.SetFamily.Shadow
public import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# Lubell-Yamamoto-Meshalkin inequality and Sperner's theorem

This file proves the local LYM and LYM inequalities as well as Sperner's theorem.

## Main declarations

* `Finset.local_lubell_yamamoto_meshalkin_inequality_div`: Local Lubell-Yamamoto-Meshalkin
  inequality. The shadow of a set `𝒜` in a layer takes a greater proportion of its layer than `𝒜`
  does.
* `Finset.lubell_yamamoto_meshalkin_inequality_sum_card_div_choose`: Lubell-Yamamoto-Meshalkin
  inequality. The sum of densities of `𝒜` in each layer is at most `1` for any antichain `𝒜`.
* `IsAntichain.sperner`: Sperner's theorem. The size of any antichain in `Finset α` is at most the
  size of the maximal layer of `Finset α`. It is a corollary of
  `lubell_yamamoto_meshalkin_inequality_sum_card_div_choose`.

## TODO

Prove upward local LYM.

Provide equality cases. Local LYM gives that the equality case of LYM and Sperner is precisely when
`𝒜` is a middle layer.

`falling` could be useful more generally in grade orders.

## References

* http://b-mehta.github.io/maths-notes/iii/mich/combinatorics.pdf
* http://discretemath.imp.fu-berlin.de/DMII-2015-16/kruskal.pdf

## Tags

shadow, lym, slice, sperner, antichain
-/

@[expose] public section

open Finset Nat
open scoped FinsetFamily

variable {𝕜 α : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

namespace Finset

/-! ### Local LYM inequality -/

section LocalLYM
variable [DecidableEq α] [Fintype α] {𝒜 : Finset (Finset α)} {r : Nat}

/--
theorem `local_lubell_yamamoto_meshalkin_inequality_mul` / 定理 `local_lubell_yamamoto_meshalkin_inequality_mul`

English:
theorem local_lubell_yamamoto_meshalkin_inequality_mul
  given: (h𝒜 : (𝒜 : Set (Finset α)).Sized r)
  proof: by
  let i : DecidableRel ((· subseteq ·) : Finset α -> Finset α -> Prop) := fun _ _ => Classical.dec _
  refine card_mul_le_card_mul' (· subseteq ·) (fun s hs => ?_) (fun s hs => ?_)
  · rw [← h𝒜 hs, ← card_image_of_injOn s.erase_injOn]
    refine card_le_card ?_
    simp_rw [image_subset_iff, mem_bipartiteBelow]
    exact fun a ha => ⟨erase_mem_shadow hs ha, erase_subset _ _⟩
  refine le_trans ?_ tsub_tsub_le_tsub_add
  rw [← (Set.Sized.shadow h𝒜) hs]; rw [← card_compl]; rw [← card_image_of_injOn (insert_inj_on' _)]
  refine card_le_card fun t ht => ?_
  rw [mem_bipartiteAbove] at ht
  have : ∅ ∉ 𝒜 := by
    rw [← mem_coe]; rw [h𝒜.empty_mem_iff]; rw [coe_eq_singleton]
    rintro rfl
    rw [shadow_singleton_empty] at hs
    exact notMem_empty s hs
  have h := exists_eq_insert_iff.2 ⟨ht.2, by
    rw [(sized_shadow_iff this).1 (Set.Sized.shadow h𝒜) ht.1]; rw [(Set.Sized.shadow h𝒜) hs]⟩
  rcases h with ⟨a, ha, rfl⟩
  exact mem_image_of_mem _ (mem_compl.2 ha)

@[inherit_doc local_lubell_yamamoto_meshalkin_inequality_mul]
alias card_mul_le_card_shadow_mul := local_lubell_yamamoto_meshalkin_inequality_mul

中文:
定理 local_lubell_yamamoto_meshalkin_inequality_mul
  条件: (h𝒜 : (𝒜 : 集合 (有限集 α)).Sized r)
  证明: by
  let i : DecidableRel ((· subseteq ·) : Finset α -> Finset α -> Prop) := fun _ _ => Classical.dec _
  refine card_mul_le_card_mul' (· subseteq ·) (fun s hs => ?_) (fun s hs => ?_)
  · rw [← h𝒜 hs, ← card_image_of_injOn s.erase_injOn]
    refine card_le_card ?_
    simp_rw [image_subset_iff, mem_bipartiteBelow]
    exact fun a ha => ⟨erase_mem_shadow hs ha, erase_subset _ _⟩
  refine le_trans ?_ tsub_tsub_le_tsub_add
  rw [← (Set.Sized.shadow h𝒜) hs]; rw [← card_compl]; rw [← card_image_of_injOn (insert_inj_on' _)]
  refine card_le_card fun t ht => ?_
  rw [mem_bipartiteAbove] at ht
  have : ∅ ∉ 𝒜 := by
    rw [← mem_coe]; rw [h𝒜.empty_mem_iff]; rw [coe_eq_singleton]
    rintro rfl
    rw [shadow_singleton_empty] at hs
    exact notMem_empty s hs
  have h := exists_eq_insert_iff.2 ⟨ht.2, by
    rw [(sized_shadow_iff this).1 (Set.Sized.shadow h𝒜) ht.1]; rw [(Set.Sized.shadow h𝒜) hs]⟩
  rcases h with ⟨a, ha, rfl⟩
  exact mem_image_of_mem _ (mem_compl.2 ha)

@[inherit_doc local_lubell_yamamoto_meshalkin_inequality_mul]
alias card_mul_le_card_shadow_mul := local_lubell_yamamoto_meshalkin_inequality_mul

Depends on / 依赖: Classical, Classical.dec, DecidableRel, Finset, Set.Sized.shadow, card_compl, card_image_of_injOn, card_le_card, card_mul_le_card_mul, erase_injOn, erase_mem_shadow, erase_subset, image_subset_iff, insert_inj_on, le_trans, mem_bipartiteBelow, s.erase_injOn, shadow, simp_rw, subseteq
-/
theorem local_lubell_yamamoto_meshalkin_inequality_mul (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    #𝒜 * r <= #(∂ 𝒜) * (Fintype.card α - r + 1) := by
  let i : DecidableRel ((· subseteq ·) : Finset α -> Finset α -> Prop) := fun _ _ => Classical.dec _
  refine card_mul_le_card_mul' (· subseteq ·) (fun s hs => ?_) (fun s hs => ?_)
  · rw [← h𝒜 hs, ← card_image_of_injOn s.erase_injOn]
    refine card_le_card ?_
    simp_rw [image_subset_iff, mem_bipartiteBelow]
    exact fun a ha => ⟨erase_mem_shadow hs ha, erase_subset _ _⟩
  refine le_trans ?_ tsub_tsub_le_tsub_add
  rw [← (Set.Sized.shadow h𝒜) hs]; rw [← card_compl]; rw [← card_image_of_injOn (insert_inj_on' _)]
  refine card_le_card fun t ht => ?_
  rw [mem_bipartiteAbove] at ht
  have : ∅ ∉ 𝒜 := by
    rw [← mem_coe]; rw [h𝒜.empty_mem_iff]; rw [coe_eq_singleton]
    rintro rfl
    rw [shadow_singleton_empty] at hs
    exact notMem_empty s hs
  have h := exists_eq_insert_iff.2 ⟨ht.2, by
    rw [(sized_shadow_iff this).1 (Set.Sized.shadow h𝒜) ht.1]; rw [(Set.Sized.shadow h𝒜) hs]⟩
  rcases h with ⟨a, ha, rfl⟩
  exact mem_image_of_mem _ (mem_compl.2 ha)

@[inherit_doc local_lubell_yamamoto_meshalkin_inequality_mul]
alias card_mul_le_card_shadow_mul := local_lubell_yamamoto_meshalkin_inequality_mul

/--
theorem `local_lubell_yamamoto_meshalkin_inequality_div` / 定理 `local_lubell_yamamoto_meshalkin_inequality_div`

English:
theorem local_lubell_yamamoto_meshalkin_inequality_div
  statement: (hr : r != 0)
  proof: by
  obtain hr' | hr' := lt_or_ge (Fintype.card α) r
  · rw [choose_eq_zero_of_lt hr', cast_zero, div_zero]
    exact div_nonneg (cast_nonneg _) (cast_nonneg _)
  replace h𝒜 := local_lubell_yamamoto_meshalkin_inequality_mul h𝒜
  rw [div_le_div_iff₀] <;> norm_cast
  · rcases r with - | r
    · exact (hr rfl).elim
    rw [tsub_add_eq_add_tsub hr']; rw [add_tsub_add_eq_tsub_right] at h𝒜
    apply le_of_mul_le_mul_right _ (pos_iff_ne_zero.2 hr)
    convert! Nat.mul_le_mul_right ((Fintype.card α).choose r) h𝒜 using 1
    · simpa [mul_assoc, Nat.choose_succ_right_eq] using Or.inl (mul_comm _ _)
    · simp only [mul_assoc, choose_succ_right_eq, mul_eq_mul_left_iff]
      exact Or.inl (mul_comm _ _)
  · exact Nat.choose_pos hr'
  · exact Nat.choose_pos (r.pred_le.trans hr')

@[inherit_doc local_lubell_yamamoto_meshalkin_inequality_div]
alias card_div_choose_le_card_shadow_div_choose := local_lubell_yamamoto_meshalkin_inequality_div

中文:
定理 local_lubell_yamamoto_meshalkin_inequality_div
  结论: (hr : r != 0)
  证明: by
  obtain hr' | hr' := lt_or_ge (Fintype.card α) r
  · rw [choose_eq_zero_of_lt hr', cast_zero, div_zero]
    exact div_nonneg (cast_nonneg _) (cast_nonneg _)
  replace h𝒜 := local_lubell_yamamoto_meshalkin_inequality_mul h𝒜
  rw [div_le_div_iff₀] <;> norm_cast
  · rcases r with - | r
    · exact (hr rfl).elim
    rw [tsub_add_eq_add_tsub hr']; rw [add_tsub_add_eq_tsub_right] at h𝒜
    apply le_of_mul_le_mul_right _ (pos_iff_ne_zero.2 hr)
    convert! Nat.mul_le_mul_right ((Fintype.card α).choose r) h𝒜 using 1
    · simpa [mul_assoc, Nat.choose_succ_right_eq] using Or.inl (mul_comm _ _)
    · simp only [mul_assoc, choose_succ_right_eq, mul_eq_mul_left_iff]
      exact Or.inl (mul_comm _ _)
  · exact Nat.choose_pos hr'
  · exact Nat.choose_pos (r.pred_le.trans hr')

@[inherit_doc local_lubell_yamamoto_meshalkin_inequality_div]
alias card_div_choose_le_card_shadow_div_choose := local_lubell_yamamoto_meshalkin_inequality_div

Depends on / 依赖: Fintype, Fintype.card, Nat.mul_le_mul_right, add_tsub_add_eq_tsub_right, cast_nonneg, cast_zero, choose_eq_zero_of_lt, convert, div_nonneg, div_zero, le_of_mul_le_mul_right, local_lubell_yamamoto_meshalkin_inequality_mul, lt_or_ge, mul_le_mul_right, pos_iff_ne_zero, replace, tsub_add_eq_add_tsub
-/
theorem local_lubell_yamamoto_meshalkin_inequality_div (hr : r != 0)
    (h𝒜 : (𝒜 : Set (Finset α)).Sized r) : (#𝒜 : 𝕜) / (Fintype.card α).choose r
    <= #(∂ 𝒜) / (Fintype.card α).choose (r - 1) := by
  obtain hr' | hr' := lt_or_ge (Fintype.card α) r
  · rw [choose_eq_zero_of_lt hr', cast_zero, div_zero]
    exact div_nonneg (cast_nonneg _) (cast_nonneg _)
  replace h𝒜 := local_lubell_yamamoto_meshalkin_inequality_mul h𝒜
  rw [div_le_div_iff₀] <;> norm_cast
  · rcases r with - | r
    · exact (hr rfl).elim
    rw [tsub_add_eq_add_tsub hr']; rw [add_tsub_add_eq_tsub_right] at h𝒜
    apply le_of_mul_le_mul_right _ (pos_iff_ne_zero.2 hr)
    convert! Nat.mul_le_mul_right ((Fintype.card α).choose r) h𝒜 using 1
    · simpa [mul_assoc, Nat.choose_succ_right_eq] using Or.inl (mul_comm _ _)
    · simp only [mul_assoc, choose_succ_right_eq, mul_eq_mul_left_iff]
      exact Or.inl (mul_comm _ _)
  · exact Nat.choose_pos hr'
  · exact Nat.choose_pos (r.pred_le.trans hr')

@[inherit_doc local_lubell_yamamoto_meshalkin_inequality_div]
alias card_div_choose_le_card_shadow_div_choose := local_lubell_yamamoto_meshalkin_inequality_div

end LocalLYM

/-! ### LYM inequality -/

section LYM

section Falling

variable [DecidableEq α] (k : Nat) (𝒜 : Finset (Finset α))

/--
Definition of `falling` / `falling` 的定义

English:
definition falling
  signature: : Finset (Finset α)
  body: 𝒜.sup powersetCard k

中文:
定义 falling
  签名: : 有限集 (有限集 α)
  定义体: 𝒜.sup powersetCard k

Depends on / 依赖: powersetCard
-/
def falling : Finset (Finset α) :=
𝒜.sup powersetCard k

variable {𝒜 k} {s : Finset α}

/--
theorem `mem_falling` / 定理 `mem_falling`

English:
theorem mem_falling
  statement: s in falling k 𝒜 ↔ (exists t in 𝒜, s subseteq t) ∧ #s = k
  proof: by
  grind [falling, mem_sup]

中文:
定理 mem_falling
  结论: s in falling k 𝒜 ↔ (存在 t in 𝒜, s subseteq t) ∧ #s = k
  证明: by
  grind [falling, mem_sup]

Depends on / 依赖: falling, mem_sup
-/
theorem mem_falling : s in falling k 𝒜 ↔ (exists t in 𝒜, s subseteq t) ∧ #s = k := by
  grind [falling, mem_sup]

variable (𝒜 k)

/--
theorem `sized_falling` / 定理 `sized_falling`

English:
theorem sized_falling
  statement: (falling k 𝒜 : Set (Finset α)).Sized k
  proof: fun _ hs => (mem_falling.1 hs).2

中文:
定理 sized_falling
  结论: (falling k 𝒜 : 集合 (有限集 α)).Sized k
  证明: fun _ hs => (mem_falling.1 hs).2

Depends on / 依赖: mem_falling
-/
theorem sized_falling : (falling k 𝒜 : Set (Finset α)).Sized k := fun _ hs => (mem_falling.1 hs).2

/--
theorem `slice_subset_falling` / 定理 `slice_subset_falling`

English:
theorem slice_subset_falling
  statement: 𝒜 # k subseteq falling k 𝒜
  proof: fun s hs =>
mem_falling.2 (mem_slice.1 hs).imp_left fun h => ⟨s, h, Subset.refl _⟩

中文:
定理 slice_subset_falling
  结论: 𝒜 # k subseteq falling k 𝒜
  证明: fun s hs =>
mem_falling.2 (mem_slice.1 hs).imp_left fun h => ⟨s, h, Subset.refl _⟩
-/
theorem slice_subset_falling : 𝒜 # k subseteq falling k 𝒜 := fun s hs =>
mem_falling.2 (mem_slice.1 hs).imp_left fun h => ⟨s, h, Subset.refl _⟩

/--
theorem `falling_zero_subset` / 定理 `falling_zero_subset`

English:
theorem falling_zero_subset
  statement: falling 0 𝒜 subseteq {∅}
  proof: subset_singleton_iff'.2 fun _ ht => card_eq_zero.1 sized_falling _ _ ht

中文:
定理 falling_zero_subset
  结论: falling 0 𝒜 subseteq {∅}
  证明: subset_singleton_iff'.2 fun _ ht => card_eq_zero.1 sized_falling _ _ ht

Depends on / 依赖: card_eq_zero, sized_falling, subset_singleton_iff
-/
theorem falling_zero_subset : falling 0 𝒜 subseteq {∅} :=
subset_singleton_iff'.2 fun _ ht => card_eq_zero.1 sized_falling _ _ ht

/--
theorem `slice_union_shadow_falling_succ` / 定理 `slice_union_shadow_falling_succ`

English:
theorem slice_union_shadow_falling_succ
  statement: 𝒜 # k union ∂ (falling (k + 1) 𝒜) = falling k 𝒜
  proof: by
  ext s
  simp_rw [mem_union, mem_slice, mem_shadow_iff, mem_falling]
  constructor
  · rintro (h | ⟨s, ⟨⟨t, ht, hst⟩, hs⟩, a, ha, rfl⟩)
    · exact ⟨⟨s, h.1, Subset.refl _⟩, h.2⟩
    refine ⟨⟨t, ht, (erase_subset _ _).trans hst⟩, ?_⟩
    rw [card_erase_of_mem ha]; rw [hs]
    rfl
  · rintro ⟨⟨t, ht, hst⟩, hs⟩
    by_cases h : s in 𝒜
    · exact Or.inl ⟨h, hs⟩
    obtain ⟨a, ha, hst⟩ := ssubset_iff.1 (ssubset_of_subset_of_ne hst (ht.ne_of_notMem h).symm)
    refine Or.inr ⟨insert a s, ⟨⟨t, ht, hst⟩, ?_⟩, a, mem_insert_self _ _, erase_insert ha⟩
    rw [card_insert_of_notMem ha]; rw [hs]

中文:
定理 slice_union_shadow_falling_succ
  结论: 𝒜 # k union ∂ (falling (k + 1) 𝒜) = falling k 𝒜
  证明: by
  ext s
  simp_rw [mem_union, mem_slice, mem_shadow_iff, mem_falling]
  constructor
  · rintro (h | ⟨s, ⟨⟨t, ht, hst⟩, hs⟩, a, ha, rfl⟩)
    · exact ⟨⟨s, h.1, Subset.refl _⟩, h.2⟩
    refine ⟨⟨t, ht, (erase_subset _ _).trans hst⟩, ?_⟩
    rw [card_erase_of_mem ha]; rw [hs]
    rfl
  · rintro ⟨⟨t, ht, hst⟩, hs⟩
    by_cases h : s in 𝒜
    · exact Or.inl ⟨h, hs⟩
    obtain ⟨a, ha, hst⟩ := ssubset_iff.1 (ssubset_of_subset_of_ne hst (ht.ne_of_notMem h).symm)
    refine Or.inr ⟨insert a s, ⟨⟨t, ht, hst⟩, ?_⟩, a, mem_insert_self _ _, erase_insert ha⟩
    rw [card_insert_of_notMem ha]; rw [hs]

Depends on / 依赖: Or.inl, Or.inr, Subset, Subset.refl, card_erase_of_mem, erase_subset, ht.ne_of_notMem, insert, mem_falling, mem_insert_self, mem_shadow_iff, mem_slice, mem_union, ne_of_notMem, simp_rw, ssubset_iff, ssubset_of_subset_of_ne
-/
theorem slice_union_shadow_falling_succ : 𝒜 # k union ∂ (falling (k + 1) 𝒜) = falling k 𝒜 := by
  ext s
  simp_rw [mem_union, mem_slice, mem_shadow_iff, mem_falling]
  constructor
  · rintro (h | ⟨s, ⟨⟨t, ht, hst⟩, hs⟩, a, ha, rfl⟩)
    · exact ⟨⟨s, h.1, Subset.refl _⟩, h.2⟩
    refine ⟨⟨t, ht, (erase_subset _ _).trans hst⟩, ?_⟩
    rw [card_erase_of_mem ha]; rw [hs]
    rfl
  · rintro ⟨⟨t, ht, hst⟩, hs⟩
    by_cases h : s in 𝒜
    · exact Or.inl ⟨h, hs⟩
    obtain ⟨a, ha, hst⟩ := ssubset_iff.1 (ssubset_of_subset_of_ne hst (ht.ne_of_notMem h).symm)
    refine Or.inr ⟨insert a s, ⟨⟨t, ht, hst⟩, ?_⟩, a, mem_insert_self _ _, erase_insert ha⟩
    rw [card_insert_of_notMem ha]; rw [hs]

variable {𝒜 k}

/--
theorem `IsAntichain.disjoint_slice_shadow_falling` / 定理 `IsAntichain.disjoint_slice_shadow_falling`

English:
theorem IsAntichain.disjoint_slice_shadow_falling
  statement: {m n : Nat}
  proof: disjoint_right.2 fun s h₁ h₂ => by
    simp_rw [mem_shadow_iff, mem_falling] at h₁
    obtain ⟨s, ⟨⟨t, ht, hst⟩, _⟩, a, ha, rfl⟩ := h₁
    refine h𝒜 (slice_subset h₂) ht ?_ ((erase_subset _ _).trans hst)
    rintro rfl
    exact notMem_erase _ _ (hst ha)

中文:
定理 IsAntichain.disjoint_slice_shadow_falling
  结论: {m n : 自然数}
  证明: disjoint_right.2 fun s h₁ h₂ => by
    simp_rw [mem_shadow_iff, mem_falling] at h₁
    obtain ⟨s, ⟨⟨t, ht, hst⟩, _⟩, a, ha, rfl⟩ := h₁
    refine h𝒜 (slice_subset h₂) ht ?_ ((erase_subset _ _).trans hst)
    rintro rfl
    exact notMem_erase _ _ (hst ha)

Depends on / 依赖: disjoint_right, erase_subset, mem_falling, mem_shadow_iff, notMem_erase, simp_rw, slice_subset
-/
theorem IsAntichain.disjoint_slice_shadow_falling {m n : Nat}
    (h𝒜 : IsAntichain (· subseteq ·) (𝒜 : Set (Finset α))) : Disjoint (𝒜 # m) (∂ (falling n 𝒜)) :=
  disjoint_right.2 fun s h₁ h₂ => by
    simp_rw [mem_shadow_iff, mem_falling] at h₁
    obtain ⟨s, ⟨⟨t, ht, hst⟩, _⟩, a, ha, rfl⟩ := h₁
    refine h𝒜 (slice_subset h₂) ht ?_ ((erase_subset _ _).trans hst)
    rintro rfl
    exact notMem_erase _ _ (hst ha)

/--
theorem `le_card_falling_div_choose` / 定理 `le_card_falling_div_choose`

English:
theorem le_card_falling_div_choose
  statement: [Fintype α] (hk : k <= Fintype.card α)
  proof: by
  induction k with
  | zero =>
    simp only [cast_one, cast_le, sum_singleton, div_one, choose_self, range_one,
      zero_add, range_one, sum_singleton,
      choose_self, cast_one, div_one, cast_le, tsub_zero]
    exact card_le_card (slice_subset_falling _ _)
  | succ k ih =>
    rw [sum_range_succ]; rw [← slice_union_shadow_falling_succ]; rw [card_union_of_disjoint (IsAntichain.disjoint_slice_shadow_falling h𝒜)]; rw [cast_add]; rw [_root_.add_div]; rw [add_comm]
    rw [← tsub_tsub]; rw [tsub_add_cancel_of_le (le_tsub_of_add_le_left hk)]
    grw [ih <| le_of_succ_le hk, local_lubell_yamamoto_meshalkin_inequality_div
(tsub_pos_iff_lt.2 <| Nat.succ_le_iff.1 hk).ne' sized_falling _ _]

中文:
定理 le_card_falling_div_choose
  结论: [有限类型 α] (hk : k <= 有限类型.card α)
  证明: by
  induction k with
  | zero =>
    simp only [cast_one, cast_le, sum_singleton, div_one, choose_self, range_one,
      zero_add, range_one, sum_singleton,
      choose_self, cast_one, div_one, cast_le, tsub_zero]
    exact card_le_card (slice_subset_falling _ _)
  | succ k ih =>
    rw [sum_range_succ]; rw [← slice_union_shadow_falling_succ]; rw [card_union_of_disjoint (IsAntichain.disjoint_slice_shadow_falling h𝒜)]; rw [cast_add]; rw [_root_.add_div]; rw [add_comm]
    rw [← tsub_tsub]; rw [tsub_add_cancel_of_le (le_tsub_of_add_le_left hk)]
    grw [ih <| le_of_succ_le hk, local_lubell_yamamoto_meshalkin_inequality_div
(tsub_pos_iff_lt.2 <| Nat.succ_le_iff.1 hk).ne' sized_falling _ _]

Depends on / 依赖: IsAntichain, IsAntichain.disjoint_slice_shadow_falling, _root_, _root_.add_div, add_comm, add_div, card_le_card, card_union_of_disjoint, cast_add, cast_le, cast_one, choose_self, disjoint_slice_shadow_falling, div_one, le_tsub_of_, range_one, slice_subset_falling, slice_union_shadow_falling_succ, sum_range_succ, sum_singleton
-/
theorem le_card_falling_div_choose [Fintype α] (hk : k <= Fintype.card α)
    (h𝒜 : IsAntichain (· subseteq ·) (𝒜 : Set (Finset α))) :
    (∑ r in range (k + 1),
        (#(𝒜 # (Fintype.card α - r)) : 𝕜) / (Fintype.card α).choose (Fintype.card α - r)) <=
      (falling (Fintype.card α - k) 𝒜).card / (Fintype.card α).choose (Fintype.card α - k) := by
  induction k with
  | zero =>
    simp only [cast_one, cast_le, sum_singleton, div_one, choose_self, range_one,
      zero_add, range_one, sum_singleton,
      choose_self, cast_one, div_one, cast_le, tsub_zero]
    exact card_le_card (slice_subset_falling _ _)
  | succ k ih =>
    rw [sum_range_succ]; rw [← slice_union_shadow_falling_succ]; rw [card_union_of_disjoint (IsAntichain.disjoint_slice_shadow_falling h𝒜)]; rw [cast_add]; rw [_root_.add_div]; rw [add_comm]
    rw [← tsub_tsub]; rw [tsub_add_cancel_of_le (le_tsub_of_add_le_left hk)]
    grw [ih <| le_of_succ_le hk, local_lubell_yamamoto_meshalkin_inequality_div
(tsub_pos_iff_lt.2 <| Nat.succ_le_iff.1 hk).ne' sized_falling _ _]

end Falling

variable [Fintype α] {𝒜 : Finset (Finset α)}

/--
theorem `lubell_yamamoto_meshalkin_inequality_sum_card_div_choose` / 定理 `lubell_yamamoto_meshalkin_inequality_sum_card_div_choose`

English:
theorem lubell_yamamoto_meshalkin_inequality_sum_card_div_choose
  proof: by
  classical
    rw [← sum_flip]
    refine (le_card_falling_div_choose le_rfl h𝒜).trans ?_
    rw [div_le_iff₀] <;> norm_cast
    · simpa only [Nat.sub_self, one_mul, Nat.choose_zero_right, falling] using
        Set.Sized.card_le (sized_falling 0 𝒜)
    · rw [tsub_self, choose_zero_right]
      exact zero_lt_one

@[inherit_doc lubell_yamamoto_meshalkin_inequality_sum_card_div_choose]
alias sum_card_slice_div_choose_le_one := lubell_yamamoto_meshalkin_inequality_sum_card_div_choose

中文:
定理 lubell_yamamoto_meshalkin_inequality_sum_card_div_choose
  证明: by
  classical
    rw [← sum_flip]
    refine (le_card_falling_div_choose le_rfl h𝒜).trans ?_
    rw [div_le_iff₀] <;> norm_cast
    · simpa only [Nat.sub_self, one_mul, Nat.choose_zero_right, falling] using
        Set.Sized.card_le (sized_falling 0 𝒜)
    · rw [tsub_self, choose_zero_right]
      exact zero_lt_one

@[inherit_doc lubell_yamamoto_meshalkin_inequality_sum_card_div_choose]
alias sum_card_slice_div_choose_le_one := lubell_yamamoto_meshalkin_inequality_sum_card_div_choose

Depends on / 依赖: Nat.choose_zero_right, Nat.sub_self, Set.Sized.card_le, card_le, choose_zero_right, classical, falling, le_card_falling_div_choose, le_rfl, one_mul, sized_falling, sub_self, sum_flip, tsub_self, zero_lt_one
-/
theorem lubell_yamamoto_meshalkin_inequality_sum_card_div_choose
    (h𝒜 : IsAntichain (· subseteq ·) (𝒜 : Set (Finset α))) :
    ∑ r in range (Fintype.card α + 1), (#(𝒜 # r) / (Fintype.card α).choose r : 𝕜) <= 1 := by
  classical
    rw [← sum_flip]
    refine (le_card_falling_div_choose le_rfl h𝒜).trans ?_
    rw [div_le_iff₀] <;> norm_cast
    · simpa only [Nat.sub_self, one_mul, Nat.choose_zero_right, falling] using
        Set.Sized.card_le (sized_falling 0 𝒜)
    · rw [tsub_self, choose_zero_right]
      exact zero_lt_one

@[inherit_doc lubell_yamamoto_meshalkin_inequality_sum_card_div_choose]
alias sum_card_slice_div_choose_le_one := lubell_yamamoto_meshalkin_inequality_sum_card_div_choose

/--
theorem `lubell_yamamoto_meshalkin_inequality_sum_inv_choose` / 定理 `lubell_yamamoto_meshalkin_inequality_sum_inv_choose`

English:
theorem lubell_yamamoto_meshalkin_inequality_sum_inv_choose
  proof: by
  calc
    _ = ∑ r in range (Fintype.card α + 1),
        ∑ s in 𝒜 with #s = r, ((Fintype.card α).choose r : 𝕜)⁻¹ := by
      rw [sum_fiberwise_of_maps_to']; simp [card_le_univ]
    _ = ∑ r in range (Fintype.card α + 1), (#(𝒜 # r) / (Fintype.card α).choose r : 𝕜) := by
      simp [slice, div_eq_mul_inv]
    _ <= 1 := lubell_yamamoto_meshalkin_inequality_sum_card_div_choose h𝒜

中文:
定理 lubell_yamamoto_meshalkin_inequality_sum_inv_choose
  证明: by
  calc
    _ = ∑ r in range (Fintype.card α + 1),
        ∑ s in 𝒜 with #s = r, ((Fintype.card α).choose r : 𝕜)⁻¹ := by
      rw [sum_fiberwise_of_maps_to']; simp [card_le_univ]
    _ = ∑ r in range (Fintype.card α + 1), (#(𝒜 # r) / (Fintype.card α).choose r : 𝕜) := by
      simp [slice, div_eq_mul_inv]
    _ <= 1 := lubell_yamamoto_meshalkin_inequality_sum_card_div_choose h𝒜

Depends on / 依赖: Fintype, Fintype.card, card_le_univ, div_eq_mul_inv, lubell_yamamoto_meshalkin_inequality_sum_card_div_choose, sum_fiberwise_of_maps_to
-/
theorem lubell_yamamoto_meshalkin_inequality_sum_inv_choose
    (h𝒜 : IsAntichain (· subseteq ·) (SetLike.coe 𝒜)) :
    ∑ s in 𝒜, ((Fintype.card α).choose #s : 𝕜)⁻¹ <= 1 := by
  calc
    _ = ∑ r in range (Fintype.card α + 1),
        ∑ s in 𝒜 with #s = r, ((Fintype.card α).choose r : 𝕜)⁻¹ := by
      rw [sum_fiberwise_of_maps_to']; simp [card_le_univ]
    _ = ∑ r in range (Fintype.card α + 1), (#(𝒜 # r) / (Fintype.card α).choose r : 𝕜) := by
      simp [slice, div_eq_mul_inv]
    _ <= 1 := lubell_yamamoto_meshalkin_inequality_sum_card_div_choose h𝒜

/-! ### Sperner's theorem -/

/--
theorem `_root_.IsAntichain.sperner` / 定理 `_root_.IsAntichain.sperner`

English:
theorem _root_.IsAntichain.sperner
  given: (h𝒜 : IsAntichain (· subseteq ·) (SetLike.coe 𝒜))
  proof: by
  have : 0 < ((Fintype.card α).choose (Fintype.card α / 2) : Rat>=0) :=
Nat.cast_pos.2 choose_pos (Nat.div_le_self _ _)
  have h := calc
    ∑ s in 𝒜, ((Fintype.card α).choose (Fintype.card α / 2) : Rat>=0)⁻¹
    _ <= ∑ s in 𝒜, ((Fintype.card α).choose #s : Rat>=0)⁻¹ := by
      gcongr with s hs
      · exact mod_cast choose_pos s.card_le_univ
      · exact choose_le_middle _ _
    _ <= 1 := lubell_yamamoto_meshalkin_inequality_sum_inv_choose h𝒜
  simpa [mul_inv_le_iff₀' this] using h

中文:
定理 _root_.IsAntichain.sperner
  条件: (h𝒜 : IsAntichain (· subseteq ·) (集合状.coe 𝒜))
  证明: by
  have : 0 < ((Fintype.card α).choose (Fintype.card α / 2) : Rat>=0) :=
Nat.cast_pos.2 choose_pos (Nat.div_le_self _ _)
  have h := calc
    ∑ s in 𝒜, ((Fintype.card α).choose (Fintype.card α / 2) : Rat>=0)⁻¹
    _ <= ∑ s in 𝒜, ((Fintype.card α).choose #s : Rat>=0)⁻¹ := by
      gcongr with s hs
      · exact mod_cast choose_pos s.card_le_univ
      · exact choose_le_middle _ _
    _ <= 1 := lubell_yamamoto_meshalkin_inequality_sum_inv_choose h𝒜
  simpa [mul_inv_le_iff₀' this] using h

Depends on / 依赖: Fintype, Fintype.card, Nat.cast_pos, Nat.div_le_self, card_le_univ, cast_pos, choose_le_middle, choose_pos, div_le_self, lubell_yamamoto_meshalkin_inequality_sum_inv_choose, mod_cast, s.card_le_univ
-/
theorem _root_.IsAntichain.sperner (h𝒜 : IsAntichain (· subseteq ·) (SetLike.coe 𝒜)) :
    #𝒜 <= (Fintype.card α).choose (Fintype.card α / 2) := by
  have : 0 < ((Fintype.card α).choose (Fintype.card α / 2) : Rat>=0) :=
Nat.cast_pos.2 choose_pos (Nat.div_le_self _ _)
  have h := calc
    ∑ s in 𝒜, ((Fintype.card α).choose (Fintype.card α / 2) : Rat>=0)⁻¹
    _ <= ∑ s in 𝒜, ((Fintype.card α).choose #s : Rat>=0)⁻¹ := by
      gcongr with s hs
      · exact mod_cast choose_pos s.card_le_univ
      · exact choose_le_middle _ _
    _ <= 1 := lubell_yamamoto_meshalkin_inequality_sum_inv_choose h𝒜
  simpa [mul_inv_le_iff₀' this] using h

end LYM
end Finset
