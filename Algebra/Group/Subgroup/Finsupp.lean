/-
Copyright (c) 2024 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Group.Subgroup.Lattice

/-! # Connection between `Subgroup.closure` and `Finsupp.prod` -/

public section

assert_not_exists Field

namespace Subgroup

variable {M : Type*} [CommGroup M] {ι : Type*} (f : ι -> M) (x : M)

@[to_additive]
/--
theorem `exists_finsupp_of_mem_closure_range` / 定理 `exists_finsupp_of_mem_closure_range`

English:
theorem exists_finsupp_of_mem_closure_range
  given: (hx : x in closure (Set.range f))
  proof: by
  classical
  induction hx using closure_induction with
  | mem x h => obtain ⟨i, rfl⟩ := h; exact ⟨Finsupp.single i 1, by simp⟩
  | one => use 0; simp
  | mul x y hx hy hx' hy' =>
    obtain ⟨⟨v, rfl⟩, w, rfl⟩ := And.intro hx' hy'
    use v + w
    rw [Finsupp.prod_add_index]
    · simp
    · si

中文:
定理 exists_finsupp_of_mem_closure_range
  条件: (hx : x in closure (Set.range f))
  证明: by
  classical
  induction hx using closure_induction with
  | mem x h => obtain ⟨i, rfl⟩ := h; exact ⟨Finsupp.single i 1, by simp⟩
  | one => use 0; simp
  | mul x y hx hy hx' hy' =>
    obtain ⟨⟨v, rfl⟩, w, rfl⟩ := And.intro hx' hy'
    use v + w
    rw [Finsupp.prod_add_index]
    · simp
    · si

Depends on / 依赖: And.intro, Finsupp, Finsupp.prod_add_index, Finsupp.prod_neg_index, Finsupp.single, classical, closure_induction, prod_add_index, prod_neg_index, single, zpow_add
-/
theorem exists_finsupp_of_mem_closure_range (hx : x in closure (Set.range f)) :
    exists a : ι ->₀ Int, x = a.prod (f · ^ ·) := by
  classical
  induction hx using closure_induction with
  | mem x h => obtain ⟨i, rfl⟩ := h; exact ⟨Finsupp.single i 1, by simp⟩
  | one => use 0; simp
  | mul x y hx hy hx' hy' =>
    obtain ⟨⟨v, rfl⟩, w, rfl⟩ := And.intro hx' hy'
    use v + w
    rw [Finsupp.prod_add_index]
    · simp
    · simp [zpow_add]
  | inv x hx hx' =>
    obtain ⟨a, rfl⟩ := hx'
    use -a
    rw [Finsupp.prod_neg_index]
    · simp
    · simp

@[to_additive]
/--
theorem `exists_of_mem_closure_range` / 定理 `exists_of_mem_closure_range`

English:
theorem exists_of_mem_closure_range
  given: [Fintype ι] (hx : x in closure (Set.range f))
  proof: by
  obtain ⟨a, rfl⟩ := exists_finsupp_of_mem_closure_range f x hx
  exact ⟨a, by simp⟩

中文:
定理 exists_of_mem_closure_range
  条件: [Fintype ι] (hx : x in closure (Set.range f))
  证明: by
  obtain ⟨a, rfl⟩ := exists_finsupp_of_mem_closure_range f x hx
  exact ⟨a, by simp⟩

Depends on / 依赖: exists_finsupp_of_mem_closure_range
-/
theorem exists_of_mem_closure_range [Fintype ι] (hx : x in closure (Set.range f)) :
    exists a : ι -> Int, x = ∏ i, f i ^ a i := by
  obtain ⟨a, rfl⟩ := exists_finsupp_of_mem_closure_range f x hx
  exact ⟨a, by simp⟩

variable {f x}

@[to_additive]
/--
theorem `mem_closure_range_iff` / 定理 `mem_closure_range_iff`

English:
theorem mem_closure_range_iff
  proof: by
  refine ⟨exists_finsupp_of_mem_closure_range f x, ?_⟩
  rintro ⟨a, rfl⟩
  exact Submonoid.prod_mem _ fun i hi => zpow_mem (subset_closure (Set.mem_range_self i)) _

@[to_additive]

中文:
定理 mem_closure_range_iff
  证明: by
  refine ⟨exists_finsupp_of_mem_closure_range f x, ?_⟩
  rintro ⟨a, rfl⟩
  exact Submonoid.prod_mem _ fun i hi => zpow_mem (subset_closure (Set.mem_range_self i)) _

@[to_additive]

Depends on / 依赖: Set.mem_range_self, Submonoid, Submonoid.prod_mem, exists_finsupp_of_mem_closure_range, mem_range_self, prod_mem, subset_closure, zpow_mem
-/
theorem mem_closure_range_iff :
    x in closure (Set.range f) ↔ exists a : ι ->₀ Int, x = a.prod (f · ^ ·) := by
  refine ⟨exists_finsupp_of_mem_closure_range f x, ?_⟩
  rintro ⟨a, rfl⟩
  exact Submonoid.prod_mem _ fun i hi => zpow_mem (subset_closure (Set.mem_range_self i)) _

@[to_additive]
/--
theorem `mem_closure_range_iff_of_fintype` / 定理 `mem_closure_range_iff_of_fintype`

English:
theorem mem_closure_range_iff_of_fintype
  given: [Fintype ι]
  proof: by
  rw [Finsupp.equivFunOnFinite.symm.exists_congr_left]; rw [mem_closure_range_iff]
  simp

@[to_additive]

中文:
定理 mem_closure_range_iff_of_fintype
  条件: [Fintype ι]
  证明: by
  rw [Finsupp.equivFunOnFinite.symm.exists_congr_left]; rw [mem_closure_range_iff]
  simp

@[to_additive]

Depends on / 依赖: Finsupp, Finsupp.equivFunOnFinite.symm.exists_congr_left, equivFunOnFinite, exists_congr_left, mem_closure_range_iff
-/
theorem mem_closure_range_iff_of_fintype [Fintype ι] :
    x in closure (Set.range f) ↔ exists a : ι -> Int, x = ∏ i, f i ^ a i := by
  rw [Finsupp.equivFunOnFinite.symm.exists_congr_left]; rw [mem_closure_range_iff]
  simp

@[to_additive]
/--
theorem `mem_closure_iff_of_fintype` / 定理 `mem_closure_iff_of_fintype`

English:
theorem mem_closure_iff_of_fintype
  given: {s : Set M} [Fintype s]
  proof: by
  conv_lhs => rw [← Subtype.range_coe (s := s)]
  exact mem_closure_range_iff_of_fintype

中文:
定理 mem_closure_iff_of_fintype
  条件: {s : Set M} [Fintype s]
  证明: by
  conv_lhs => rw [← Subtype.range_coe (s := s)]
  exact mem_closure_range_iff_of_fintype

Depends on / 依赖: Subtype, Subtype.range_coe, conv_lhs, mem_closure_range_iff_of_fintype, range_coe
-/
theorem mem_closure_iff_of_fintype {s : Set M} [Fintype s] :
    x in closure s ↔ exists a : s -> Int, x = ∏ i : s, i.1 ^ a i := by
  conv_lhs => rw [← Subtype.range_coe (s := s)]
  exact mem_closure_range_iff_of_fintype

end Subgroup
