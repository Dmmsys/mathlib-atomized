/-
Copyright (c) 2024 Yaël Dillies, Patrick Luo, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.Combinatorics.Additive.Convolution
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Qify

/-!
# Sets with very small doubling

For a finset `A` in a group, its *doubling* is `#(A * A) / #A`. This file characterises sets with
* no doubling as the sets which are either empty or translates of a subgroup.
  For the converse, use the existing facts from the pointwise API: `∅ ^ 2 = ∅` (`Finset.empty_pow`),
  `(a • H) ^ 2 = a ^ 2 • H ^ 2 = a ^ 2 • H` (`smul_pow`, `coe_set_pow`).
* doubling strictly less than `3 / 2` as the sets that are contained in a coset of a subgroup of
  size strictly less than `3 / 2 * #A`.
* doubling strictly less than `φ` as the set `A` such that `A * A⁻¹` is covered by at most some
  constant (depending only on the doubling) number of cosets of a finite subgroup of `G`.

## TODO

* Do we need versions stated using the doubling constant (`Finset.mulConst`)?
* Add characterisation of sets with doubling ≤ 2 - ε. See
  https://terrytao.wordpress.com/2011/03/12/hamidounes-freiman-kneser-theorem-for-nonabelian-groups.

## References

* [*An elementary non-commutative Freiman theorem*, Terence Tao](https://terrytao.wordpress.com/2009/11/10/an-elementary-non-commutative-freiman-theorem)
* [*Introduction to approximate groups*, Matthew Tointon][tointon2020]
-/

@[expose] public section

open MulOpposite MulAction
open scoped Pointwise RightActions

namespace Finset
variable {G : Type*} [Group G] [DecidableEq G] {K : Real} {A B S : Finset G} {a b c d x y : G}

/-! ### Doubling exactly `1` -/

@[to_additive]
/--
lemma `smul_stabilizer_of_no_doubling_aux` / 引理 `smul_stabilizer_of_no_doubling_aux`

English:
lemma smul_stabilizer_of_no_doubling_aux
  given: (hA : #(A * A) <= #A) (ha : a in A)
  proof: by
  have smul_A {a} (ha : a in A) : a •> A = A * A :=
    eq_of_subset_of_card_le (smul_finset_subset_mul ha) (by simpa)
  have A_smul {a} (ha : a in A) : A <• a = A * A :=
    eq_of_subset_of_card_le (op_smul_finset_subset_mul ha) (by simpa)
  have smul_A_eq_A_smul {a} (ha : a in A) : a •> A = A <• a := by rw [smul_A ha, A_smul ha]
  have mul_mem_A_comm {x a} (ha : a in A) : x * a in A ↔ a * x in A := by
    rw [← smul_mem_smul_finset_iff a]; rw [smul_A_eq_A_smul ha]; rw [← op_smul_eq_mul]; rw [smul_comm]; rw [smul_mem_smul_finset_iff]; rw [smul_eq_mul]
  let H := stabilizer G A
  have inv_smul_A {a} (ha : a in A) : a⁻¹ • (A : Set G) = H := by
    ext x
    rw [Set.mem_inv_smul_set_iff]; rw [smul_eq_mul]
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · simpa [← smul_A ha, mul_smul] using! smul_A hx
    · norm_cast
      rwa [← mul_mem_A_comm ha, ← smul_eq_mul, ← mem_inv_smul_finset_iff, inv_mem hx]
  refine ⟨?_, ?_⟩
  · rw [← inv_smul_A ha, smul_inv_smul]
  · rw [← inv_smul_A ha, smul_comm]
    norm_cast
    rw [← smul_A_eq_A_smul ha]; rw [inv_smul_smul]

中文:
引理 smul_stabilizer_of_no_doubling_aux
  条件: (hA : #(A * A) <= #A) (ha : a in A)
  证明: by
  have smul_A {a} (ha : a in A) : a •> A = A * A :=
    eq_of_subset_of_card_le (smul_finset_subset_mul ha) (by simpa)
  have A_smul {a} (ha : a in A) : A <• a = A * A :=
    eq_of_subset_of_card_le (op_smul_finset_subset_mul ha) (by simpa)
  have smul_A_eq_A_smul {a} (ha : a in A) : a •> A = A <• a := by rw [smul_A ha, A_smul ha]
  have mul_mem_A_comm {x a} (ha : a in A) : x * a in A ↔ a * x in A := by
    rw [← smul_mem_smul_finset_iff a]; rw [smul_A_eq_A_smul ha]; rw [← op_smul_eq_mul]; rw [smul_comm]; rw [smul_mem_smul_finset_iff]; rw [smul_eq_mul]
  let H := stabilizer G A
  have inv_smul_A {a} (ha : a in A) : a⁻¹ • (A : Set G) = H := by
    ext x
    rw [Set.mem_inv_smul_set_iff]; rw [smul_eq_mul]
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · simpa [← smul_A ha, mul_smul] using! smul_A hx
    · norm_cast
      rwa [← mul_mem_A_comm ha, ← smul_eq_mul, ← mem_inv_smul_finset_iff, inv_mem hx]
  refine ⟨?_, ?_⟩
  · rw [← inv_smul_A ha, smul_inv_smul]
  · rw [← inv_smul_A ha, smul_comm]
    norm_cast
    rw [← smul_A_eq_A_smul ha]; rw [inv_smul_smul]
-/
private lemma smul_stabilizer_of_no_doubling_aux (hA : #(A * A) <= #A) (ha : a in A) :
    a •> (stabilizer G A : Set G) = A ∧ (stabilizer G A : Set G) <• a = A := by
  have smul_A {a} (ha : a in A) : a •> A = A * A :=
    eq_of_subset_of_card_le (smul_finset_subset_mul ha) (by simpa)
  have A_smul {a} (ha : a in A) : A <• a = A * A :=
    eq_of_subset_of_card_le (op_smul_finset_subset_mul ha) (by simpa)
  have smul_A_eq_A_smul {a} (ha : a in A) : a •> A = A <• a := by rw [smul_A ha, A_smul ha]
  have mul_mem_A_comm {x a} (ha : a in A) : x * a in A ↔ a * x in A := by
    rw [← smul_mem_smul_finset_iff a]; rw [smul_A_eq_A_smul ha]; rw [← op_smul_eq_mul]; rw [smul_comm]; rw [smul_mem_smul_finset_iff]; rw [smul_eq_mul]
  let H := stabilizer G A
  have inv_smul_A {a} (ha : a in A) : a⁻¹ • (A : Set G) = H := by
    ext x
    rw [Set.mem_inv_smul_set_iff]; rw [smul_eq_mul]
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · simpa [← smul_A ha, mul_smul] using! smul_A hx
    · norm_cast
      rwa [← mul_mem_A_comm ha, ← smul_eq_mul, ← mem_inv_smul_finset_iff, inv_mem hx]
  refine ⟨?_, ?_⟩
  · rw [← inv_smul_A ha, smul_inv_smul]
  · rw [← inv_smul_A ha, smul_comm]
    norm_cast
    rw [← smul_A_eq_A_smul ha]; rw [inv_smul_smul]

/-- A non-empty set with no doubling is the left translate of its stabilizer. -/
@[to_additive /-- A non-empty set with no doubling is the left-translate of its stabilizer. -/]
/--
lemma `smul_stabilizer_of_no_doubling` / 引理 `smul_stabilizer_of_no_doubling`

English:
lemma smul_stabilizer_of_no_doubling
  given: (hA : #(A * A) <= #A) (ha : a in A)
  proof: (smul_stabilizer_of_no_doubling_aux hA ha).1

中文:
引理 smul_stabilizer_of_no_doubling
  条件: (hA : #(A * A) <= #A) (ha : a in A)
  证明: (smul_stabilizer_of_no_doubling_aux hA ha).1

Depends on / 依赖: smul_stabilizer_of_no_doubling_aux
-/
lemma smul_stabilizer_of_no_doubling (hA : #(A * A) <= #A) (ha : a in A) :
    a •> (stabilizer G A : Set G) = A := (smul_stabilizer_of_no_doubling_aux hA ha).1

/-- A non-empty set with no doubling is the right translate of its stabilizer. -/
@[to_additive /-- A non-empty set with no doubling is the right translate of its stabilizer. -/]
/--
lemma `op_smul_stabilizer_of_no_doubling` / 引理 `op_smul_stabilizer_of_no_doubling`

English:
lemma op_smul_stabilizer_of_no_doubling
  given: (hA : #(A * A) <= #A) (ha : a in A)
  proof: (smul_stabilizer_of_no_doubling_aux hA ha).2

中文:
引理 op_smul_stabilizer_of_no_doubling
  条件: (hA : #(A * A) <= #A) (ha : a in A)
  证明: (smul_stabilizer_of_no_doubling_aux hA ha).2

Depends on / 依赖: smul_stabilizer_of_no_doubling_aux
-/
lemma op_smul_stabilizer_of_no_doubling (hA : #(A * A) <= #A) (ha : a in A) :
    (stabilizer G A : Set G) <• a = A := (smul_stabilizer_of_no_doubling_aux hA ha).2


/--
lemma `big_intersection` / 引理 `big_intersection`

English:
lemma big_intersection
  given: (ha : a in B) (hb : b in B)
  proof: by
  have : #((a • A) union (b • A)) <= #(B * A) := by
    gcongr
    rw [union_subset_iff]
    exact ⟨smul_finset_subset_mul ha, smul_finset_subset_mul hb⟩
  grw [← this, card_inter_add_card_union]
  simp [card_smul_finset, two_mul]

中文:
引理 big_intersection
  条件: (ha : a in B) (hb : b in B)
  证明: by
  have : #((a • A) union (b • A)) <= #(B * A) := by
    gcongr
    rw [union_subset_iff]
    exact ⟨smul_finset_subset_mul ha, smul_finset_subset_mul hb⟩
  grw [← this, card_inter_add_card_union]
  simp [card_smul_finset, two_mul]
-/
private lemma big_intersection (ha : a in B) (hb : b in B) :
    2 * #A <= #((a • A) inter (b • A)) + #(B * A) := by
  have : #((a • A) union (b • A)) <= #(B * A) := by
    gcongr
    rw [union_subset_iff]
    exact ⟨smul_finset_subset_mul ha, smul_finset_subset_mul hb⟩
  grw [← this, card_inter_add_card_union]
  simp [card_smul_finset, two_mul]

/--
lemma `le_card_smul_inter_smul` / 引理 `le_card_smul_inter_smul`

English:
lemma le_card_smul_inter_smul
  given: (hA : #(B * A) <= K * #A) (ha : a in B) (hb : b in B)
  proof: by
  have : 2 * (#A : Real) <= #(a •> A inter b •> A) + #(B * A) := mod_cast big_intersection ha hb; linarith

中文:
引理 le_card_smul_inter_smul
  条件: (hA : #(B * A) <= K * #A) (ha : a in B) (hb : b in B)
  证明: by
  have : 2 * (#A : Real) <= #(a •> A inter b •> A) + #(B * A) := mod_cast big_intersection ha hb; linarith
-/
private lemma le_card_smul_inter_smul (hA : #(B * A) <= K * #A) (ha : a in B) (hb : b in B) :
    (2 - K) * #A <= #((a • A) inter (b • A)) := by
  have : 2 * (#A : Real) <= #(a •> A inter b •> A) + #(B * A) := mod_cast big_intersection ha hb; linarith

/--
lemma `lt_card_smul_inter_smul` / 引理 `lt_card_smul_inter_smul`

English:
lemma lt_card_smul_inter_smul
  given: (hA : #(B * A) < K * #A) (ha : a in B) (hb : b in B)
  proof: by
  have : 2 * (#A : Real) <= #(a •> A inter b •> A) + #(B * A) := mod_cast big_intersection ha hb; linarith

中文:
引理 lt_card_smul_inter_smul
  条件: (hA : #(B * A) < K * #A) (ha : a in B) (hb : b in B)
  证明: by
  have : 2 * (#A : Real) <= #(a •> A inter b •> A) + #(B * A) := mod_cast big_intersection ha hb; linarith
-/
private lemma lt_card_smul_inter_smul (hA : #(B * A) < K * #A) (ha : a in B) (hb : b in B) :
    (2 - K) * #A < #((a • A) inter (b • A)) := by
  have : 2 * (#A : Real) <= #(a •> A inter b •> A) + #(B * A) := mod_cast big_intersection ha hb; linarith

/--
lemma `le_card_mul_inv_eq` / 引理 `le_card_mul_inv_eq`

English:
lemma le_card_mul_inv_eq
  given: (hA : #(B * A) <= K * #A) (hx : x in B⁻¹ * B)
  proof: by
  simp only [mem_mul, mem_inv, exists_exists_and_eq_and] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  rw [card_mul_inv_eq_convolution_inv]
  simpa [card_smul_inter_smul] using le_card_smul_inter_smul hA ha hb

中文:
引理 le_card_mul_inv_eq
  条件: (hA : #(B * A) <= K * #A) (hx : x in B⁻¹ * B)
  证明: by
  simp only [mem_mul, mem_inv, exists_exists_and_eq_and] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  rw [card_mul_inv_eq_convolution_inv]
  simpa [card_smul_inter_smul] using le_card_smul_inter_smul hA ha hb
-/
private lemma le_card_mul_inv_eq (hA : #(B * A) <= K * #A) (hx : x in B⁻¹ * B) :
    (2 - K) * #A <= #{ab in A ×ˢ A | ab.1 * ab.2⁻¹ = x} := by
  simp only [mem_mul, mem_inv, exists_exists_and_eq_and] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  rw [card_mul_inv_eq_convolution_inv]
  simpa [card_smul_inter_smul] using le_card_smul_inter_smul hA ha hb

/--
lemma `lt_card_mul_inv_eq` / 引理 `lt_card_mul_inv_eq`

English:
lemma lt_card_mul_inv_eq
  given: (hA : #(B * A) < K * #A) (hx : x in B⁻¹ * B)
  proof: by
  simp only [mem_mul, mem_inv, exists_exists_and_eq_and] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  rw [card_mul_inv_eq_convolution_inv]
  simpa [card_smul_inter_smul] using lt_card_smul_inter_smul hA ha hb

中文:
引理 lt_card_mul_inv_eq
  条件: (hA : #(B * A) < K * #A) (hx : x in B⁻¹ * B)
  证明: by
  simp only [mem_mul, mem_inv, exists_exists_and_eq_and] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  rw [card_mul_inv_eq_convolution_inv]
  simpa [card_smul_inter_smul] using lt_card_smul_inter_smul hA ha hb
-/
private lemma lt_card_mul_inv_eq (hA : #(B * A) < K * #A) (hx : x in B⁻¹ * B) :
    (2 - K) * #A < #{ab in A ×ˢ A | ab.1 * ab.2⁻¹ = x} := by
  simp only [mem_mul, mem_inv, exists_exists_and_eq_and] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  rw [card_mul_inv_eq_convolution_inv]
  simpa [card_smul_inter_smul] using lt_card_smul_inter_smul hA ha hb

/--
lemma `mul_inv_eq_inv_mul_of_doubling_lt_two_aux` / 引理 `mul_inv_eq_inv_mul_of_doubling_lt_two_aux`

English:
lemma mul_inv_eq_inv_mul_of_doubling_lt_two_aux
  given: (h : #(A * A) < 2 * #A)
  proof: by
  intro z
  simp only [mem_mul, forall_exists_index, and_imp, mem_inv,
    exists_exists_and_eq_and]
  rintro x hx y hy rfl
  have ⟨t, ht⟩ : (x • A inter y • A).Nonempty := by
    simpa using lt_card_smul_inter_smul (K := 2) (mod_cast h) hx hy
  simp only [mem_inter, mem_smul_finset, smul_eq_mul] at ht
  obtain ⟨⟨z, hz, hzxwy⟩, w, hw, rfl⟩ := ht
  refine ⟨z, hz, w, hw, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]; rw [mul_assoc]; rw [← hzxwy]; rw [inv_mul_cancel_left]

中文:
引理 mul_inv_eq_inv_mul_of_doubling_lt_two_aux
  条件: (h : #(A * A) < 2 * #A)
  证明: by
  intro z
  simp only [mem_mul, forall_exists_index, and_imp, mem_inv,
    exists_exists_and_eq_and]
  rintro x hx y hy rfl
  have ⟨t, ht⟩ : (x • A inter y • A).Nonempty := by
    simpa using lt_card_smul_inter_smul (K := 2) (mod_cast h) hx hy
  simp only [mem_inter, mem_smul_finset, smul_eq_mul] at ht
  obtain ⟨⟨z, hz, hzxwy⟩, w, hw, rfl⟩ := ht
  refine ⟨z, hz, w, hw, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]; rw [mul_assoc]; rw [← hzxwy]; rw [inv_mul_cancel_left]
-/
private lemma mul_inv_eq_inv_mul_of_doubling_lt_two_aux (h : #(A * A) < 2 * #A) :
    A⁻¹ * A subseteq A * A⁻¹ := by
  intro z
  simp only [mem_mul, forall_exists_index, and_imp, mem_inv,
    exists_exists_and_eq_and]
  rintro x hx y hy rfl
  have ⟨t, ht⟩ : (x • A inter y • A).Nonempty := by
    simpa using lt_card_smul_inter_smul (K := 2) (mod_cast h) hx hy
  simp only [mem_inter, mem_smul_finset, smul_eq_mul] at ht
  obtain ⟨⟨z, hz, hzxwy⟩, w, hw, rfl⟩ := ht
  refine ⟨z, hz, w, hw, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]; rw [mul_assoc]; rw [← hzxwy]; rw [inv_mul_cancel_left]

-- TODO: is there a way to get wlog to make `mul_inv_eq_inv_mul_of_doubling_lt_two_aux` a goal?
-- i.e. wlog in the target rather than hypothesis
-- (BM: third time seeing this pattern)
-- I'm thinking something like wlog_suffices, where I could write
-- wlog_suffices : A⁻¹ * A ⊆ A * A⁻¹
-- which reverts *everything* (just like wlog does) and makes the side goal A⁻¹ * A = A * A⁻¹
-- under the assumption A⁻¹ * A ⊆ A * A⁻¹
-- and changes the main goal to A⁻¹ * A ⊆ A * A⁻¹
/--
lemma `mul_inv_eq_inv_mul_of_doubling_lt_two` / 引理 `mul_inv_eq_inv_mul_of_doubling_lt_two`

English:
lemma mul_inv_eq_inv_mul_of_doubling_lt_two
  given: (h : #(A * A) < 2 * #A)
  statement: A * A⁻¹ = A⁻¹ * A
  proof: by
  refine Subset.antisymm ?_ (mul_inv_eq_inv_mul_of_doubling_lt_two_aux h)
  simpa using
    mul_inv_eq_inv_mul_of_doubling_lt_two_aux (A := A⁻¹) (by simpa [← mul_inv_rev] using h)

中文:
引理 mul_inv_eq_inv_mul_of_doubling_lt_two
  条件: (h : #(A * A) < 2 * #A)
  结论: A * A⁻¹ = A⁻¹ * A
  证明: by
  refine Subset.antisymm ?_ (mul_inv_eq_inv_mul_of_doubling_lt_two_aux h)
  simpa using
    mul_inv_eq_inv_mul_of_doubling_lt_two_aux (A := A⁻¹) (by simpa [← mul_inv_rev] using h)

Depends on / 依赖: Subset, Subset.antisymm, antisymm, mul_inv_eq_inv_mul_of_doubling_lt_two_aux, mul_inv_rev
-/
lemma mul_inv_eq_inv_mul_of_doubling_lt_two (h : #(A * A) < 2 * #A) : A * A⁻¹ = A⁻¹ * A := by
  refine Subset.antisymm ?_ (mul_inv_eq_inv_mul_of_doubling_lt_two_aux h)
  simpa using
    mul_inv_eq_inv_mul_of_doubling_lt_two_aux (A := A⁻¹) (by simpa [← mul_inv_rev] using h)

/--
lemma `weaken_doubling` / 引理 `weaken_doubling`

English:
lemma weaken_doubling
  given: (h : #(A * A) < (3 / 2 : Rat) * #A)
  statement: #(A * A) < 2 * #A
  proof: by
  rw [← Nat.cast_lt (α := Rat)]; rw [Nat.cast_mul]; rw [Nat.cast_two]
  linarith only [h]

中文:
引理 weaken_doubling
  条件: (h : #(A * A) < (3 / 2 : 有理数) * #A)
  结论: #(A * A) < 2 * #A
  证明: by
  rw [← Nat.cast_lt (α := Rat)]; rw [Nat.cast_mul]; rw [Nat.cast_two]
  linarith only [h]
-/
private lemma weaken_doubling (h : #(A * A) < (3 / 2 : Rat) * #A) : #(A * A) < 2 * #A := by
  rw [← Nat.cast_lt (α := Rat)]; rw [Nat.cast_mul]; rw [Nat.cast_two]
  linarith only [h]

/--
lemma `nonempty_of_doubling` / 引理 `nonempty_of_doubling`

English:
lemma nonempty_of_doubling
  given: (h : #(A * A) < (3 / 2 : Rat) * #A)
  statement: A.Nonempty
  proof: by
  by_contra! rfl
  simp at h

中文:
引理 nonempty_of_doubling
  条件: (h : #(A * A) < (3 / 2 : 有理数) * #A)
  结论: A.非空
  证明: by
  by_contra! rfl
  simp at h
-/
private lemma nonempty_of_doubling (h : #(A * A) < (3 / 2 : Rat) * #A) : A.Nonempty := by
  by_contra! rfl
  simp at h

/--
Definition of `invMulSubgroup` / `invMulSubgroup` 的定义

English:
definition invMulSubgroup
  signature: (A : Finset G) (h : #(A * A) < (3 / 2 : Rat) * #A)
  body: A⁻¹ * A
  one_mem' := by
    have ⟨x, hx⟩ : A.Nonempty := nonempty_of_doubling h
    exact ⟨x⁻¹, inv_mem_inv hx, x, by simp [hx]⟩
  inv_mem' := by
    intro x
    simp only [Set.mem_mul, Set.mem_inv, coe_inv, forall_exists_index, mem_coe,
      and_imp]
    rintro a ha b hb rfl
    exact ⟨b⁻¹, by simpa using hb, a⁻¹, ha, by simp⟩
  mul_mem' := by
    norm_cast
    have h₁ x (hx : x in A) y (hy : y in A) : (1 / 2 : Rat) * #A < #(x • A inter y • A) := by
      convert! lt_card_smul_inter_smul (by simpa using Rat.cast_strictMono (K := Real) h) hx hy
      norm_num
      simp [← Rat.cast_lt (K := Real)]
    intro a c ha hc
    simp only [mem_mul, mem_inv'] at ha hc
    obtain ⟨a, ha, b, hb, rfl⟩ := ha
    obtain ⟨c, hc, d, hd, rfl⟩ := hc
    have h₂ : (1 / 2 : Rat) * #A < #(A inter (a * b)⁻¹ • A) := by
      refine (h₁ b hb _ ha).trans_le ?_
      rw [← card_smul_finset b⁻¹]
      simp [smul_smul, smul_finset_inter]
    have h₃ : (1 / 2 : Rat) * #A < #(A inter (c * d) • A) := by
      refine (h₁ _ hc d hd).trans_le ?_
      rw [← card_smul_finset c]
      simp [smul_smul, smul_finset_inter]
    have ⟨t, ht⟩ : ((A inter (c * d) • A) inter (A inter (a * b)⁻¹ • A)).Nonempty := by
      rw [← card_pos]; rw [← Nat.cast_pos (α := Rat)]
      have := card_inter_add_card_union (A inter (c * d) • A) (A inter (a * b)⁻¹ • A)
      rw [← Nat.cast_inj (R := Rat)]; rw [Nat.cast_add]; rw [Nat.cast_add] at this
      have : (#((A inter (c * d) • A) union (A inter (a * b)⁻¹ • A)) : Rat) <= #A := by
        rw [Nat.cast_le]; rw [← inter_union_distrib_left]
        exact card_le_card inter_subset_left
      linarith
    simp only [inter_inter_inter_comm, inter_self, mem_inter, ← inv_smul_mem_iff, inv_inv,
      smul_eq_mul, mul_assoc, mul_inv_rev] at ht
    rw [← mul_inv_eq_inv_mul_of_doubling_lt_two (weaken_doubling h)]; rw [mem_mul]
    exact ⟨a * b * t, by simp [ht, mul_assoc], ((c * d)⁻¹ * t)⁻¹, by simp [ht, mul_assoc]⟩

中文:
定义 invMulSubgroup
  签名: (A : 有限集 G) (h : #(A * A) < (3 / 2 : 有理数) * #A)
  定义体: A⁻¹ * A
  one_mem' := by
    have ⟨x, hx⟩ : A.Nonempty := nonempty_of_doubling h
    exact ⟨x⁻¹, inv_mem_inv hx, x, by simp [hx]⟩
  inv_mem' := by
    intro x
    simp only [Set.mem_mul, Set.mem_inv, coe_inv, forall_exists_index, mem_coe,
      and_imp]
    rintro a ha b hb rfl
    exact ⟨b⁻¹, by simpa using hb, a⁻¹, ha, by simp⟩
  mul_mem' := by
    norm_cast
    have h₁ x (hx : x in A) y (hy : y in A) : (1 / 2 : Rat) * #A < #(x • A inter y • A) := by
      convert! lt_card_smul_inter_smul (by simpa using Rat.cast_strictMono (K := Real) h) hx hy
      norm_num
      simp [← Rat.cast_lt (K := Real)]
    intro a c ha hc
    simp only [mem_mul, mem_inv'] at ha hc
    obtain ⟨a, ha, b, hb, rfl⟩ := ha
    obtain ⟨c, hc, d, hd, rfl⟩ := hc
    have h₂ : (1 / 2 : Rat) * #A < #(A inter (a * b)⁻¹ • A) := by
      refine (h₁ b hb _ ha).trans_le ?_
      rw [← card_smul_finset b⁻¹]
      simp [smul_smul, smul_finset_inter]
    have h₃ : (1 / 2 : Rat) * #A < #(A inter (c * d) • A) := by
      refine (h₁ _ hc d hd).trans_le ?_
      rw [← card_smul_finset c]
      simp [smul_smul, smul_finset_inter]
    have ⟨t, ht⟩ : ((A inter (c * d) • A) inter (A inter (a * b)⁻¹ • A)).Nonempty := by
      rw [← card_pos]; rw [← Nat.cast_pos (α := Rat)]
      have := card_inter_add_card_union (A inter (c * d) • A) (A inter (a * b)⁻¹ • A)
      rw [← Nat.cast_inj (R := Rat)]; rw [Nat.cast_add]; rw [Nat.cast_add] at this
      have : (#((A inter (c * d) • A) union (A inter (a * b)⁻¹ • A)) : Rat) <= #A := by
        rw [Nat.cast_le]; rw [← inter_union_distrib_left]
        exact card_le_card inter_subset_left
      linarith
    simp only [inter_inter_inter_comm, inter_self, mem_inter, ← inv_smul_mem_iff, inv_inv,
      smul_eq_mul, mul_assoc, mul_inv_rev] at ht
    rw [← mul_inv_eq_inv_mul_of_doubling_lt_two (weaken_doubling h)]; rw [mem_mul]
    exact ⟨a * b * t, by simp [ht, mul_assoc], ((c * d)⁻¹ * t)⁻¹, by simp [ht, mul_assoc]⟩
-/
def invMulSubgroup (A : Finset G) (h : #(A * A) < (3 / 2 : Rat) * #A) : Subgroup G where
  carrier := A⁻¹ * A
  one_mem' := by
    have ⟨x, hx⟩ : A.Nonempty := nonempty_of_doubling h
    exact ⟨x⁻¹, inv_mem_inv hx, x, by simp [hx]⟩
  inv_mem' := by
    intro x
    simp only [Set.mem_mul, Set.mem_inv, coe_inv, forall_exists_index, mem_coe,
      and_imp]
    rintro a ha b hb rfl
    exact ⟨b⁻¹, by simpa using hb, a⁻¹, ha, by simp⟩
  mul_mem' := by
    norm_cast
    have h₁ x (hx : x in A) y (hy : y in A) : (1 / 2 : Rat) * #A < #(x • A inter y • A) := by
      convert! lt_card_smul_inter_smul (by simpa using Rat.cast_strictMono (K := Real) h) hx hy
      norm_num
      simp [← Rat.cast_lt (K := Real)]
    intro a c ha hc
    simp only [mem_mul, mem_inv'] at ha hc
    obtain ⟨a, ha, b, hb, rfl⟩ := ha
    obtain ⟨c, hc, d, hd, rfl⟩ := hc
    have h₂ : (1 / 2 : Rat) * #A < #(A inter (a * b)⁻¹ • A) := by
      refine (h₁ b hb _ ha).trans_le ?_
      rw [← card_smul_finset b⁻¹]
      simp [smul_smul, smul_finset_inter]
    have h₃ : (1 / 2 : Rat) * #A < #(A inter (c * d) • A) := by
      refine (h₁ _ hc d hd).trans_le ?_
      rw [← card_smul_finset c]
      simp [smul_smul, smul_finset_inter]
    have ⟨t, ht⟩ : ((A inter (c * d) • A) inter (A inter (a * b)⁻¹ • A)).Nonempty := by
      rw [← card_pos]; rw [← Nat.cast_pos (α := Rat)]
      have := card_inter_add_card_union (A inter (c * d) • A) (A inter (a * b)⁻¹ • A)
      rw [← Nat.cast_inj (R := Rat)]; rw [Nat.cast_add]; rw [Nat.cast_add] at this
      have : (#((A inter (c * d) • A) union (A inter (a * b)⁻¹ • A)) : Rat) <= #A := by
        rw [Nat.cast_le]; rw [← inter_union_distrib_left]
        exact card_le_card inter_subset_left
      linarith
    simp only [inter_inter_inter_comm, inter_self, mem_inter, ← inv_smul_mem_iff, inv_inv,
      smul_eq_mul, mul_assoc, mul_inv_rev] at ht
    rw [← mul_inv_eq_inv_mul_of_doubling_lt_two (weaken_doubling h)]; rw [mem_mul]
    exact ⟨a * b * t, by simp [ht, mul_assoc], ((c * d)⁻¹ * t)⁻¹, by simp [ht, mul_assoc]⟩

/--
lemma `invMulSubgroup_eq_inv_mul` / 引理 `invMulSubgroup_eq_inv_mul`

English:
lemma invMulSubgroup_eq_inv_mul
  given: (A : Finset G) (h)
  statement: (invMulSubgroup A h : Set G) = A⁻¹ * A
  proof: rfl

中文:
引理 invMulSubgroup_eq_inv_mul
  条件: (A : 有限集 G) (h)
  结论: (invMulSubgroup A h : 集合 G) = A⁻¹ * A
  证明: rfl
-/
lemma invMulSubgroup_eq_inv_mul (A : Finset G) (h) : (invMulSubgroup A h : Set G) = A⁻¹ * A := rfl

/--
lemma `invMulSubgroup_eq_mul_inv` / 引理 `invMulSubgroup_eq_mul_inv`

English:
lemma invMulSubgroup_eq_mul_inv
  given: (A : Finset G) (h)
  statement: (invMulSubgroup A h : Set G) = A * A⁻¹
  proof: by
  rw [invMulSubgroup_eq_inv_mul]; rw [eq_comm]
  norm_cast
  exact mul_inv_eq_inv_mul_of_doubling_lt_two (by qify at h ⊢; linarith)

中文:
引理 invMulSubgroup_eq_mul_inv
  条件: (A : 有限集 G) (h)
  结论: (invMulSubgroup A h : 集合 G) = A * A⁻¹
  证明: by
  rw [invMulSubgroup_eq_inv_mul]; rw [eq_comm]
  norm_cast
  exact mul_inv_eq_inv_mul_of_doubling_lt_two (by qify at h ⊢; linarith)

Depends on / 依赖: eq_comm, invMulSubgroup_eq_inv_mul, mul_inv_eq_inv_mul_of_doubling_lt_two
-/
lemma invMulSubgroup_eq_mul_inv (A : Finset G) (h) : (invMulSubgroup A h : Set G) = A * A⁻¹ := by
  rw [invMulSubgroup_eq_inv_mul]; rw [eq_comm]
  norm_cast
  exact mul_inv_eq_inv_mul_of_doubling_lt_two (by qify at h ⊢; linarith)

instance (A : Finset G) (h) : Fintype (invMulSubgroup A h) := by
  simp only [invMulSubgroup, ← coe_mul, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
    mem_coe]
  infer_instance

/--
lemma `weak_invMulSubgroup_bound` / 引理 `weak_invMulSubgroup_bound`

English:
lemma weak_invMulSubgroup_bound
  given: (h : #(A * A) < (3 / 2 : Rat) * #A)
  proof: by
  have h₀ : A.Nonempty := nonempty_of_doubling h
  have h₁ a (ha : a in A⁻¹ * A) : (1 / 2 : Rat) * #A < #{xy in A ×ˢ A | xy.1 * xy.2⁻¹ = a} := by
    convert! lt_card_mul_inv_eq (by simpa using Rat.cast_strictMono (K := Real) h) ha
    norm_num
    simp [← Rat.cast_lt (K := Real)]
  have h₂ : forall x in A ×ˢ A, (fun ⟨x, y⟩ => x * y⁻¹) x in A⁻¹ * A := by
    rw [← mul_inv_eq_inv_mul_of_doubling_lt_two (weaken_doubling h)]
    simp only [mem_product, Prod.forall, mem_mul, and_imp, mem_inv]
    intro a b ha hb
    exact ⟨a, ha, b⁻¹, by simp [hb], rfl⟩
  have : ((1 / 2 : Rat) * #A) * #(A⁻¹ * A) < (#A : Rat) ^ 2 := by
    rw [← Nat.cast_pow]; rw [sq]; rw [← card_product]; rw [card_eq_sum_card_fiberwise h₂]; rw [Nat.cast_sum]
    refine (sum_lt_sum_of_nonempty (by simp [h₀]) h₁).trans_eq' ?_
    simp only [sum_const, nsmul_eq_mul, mul_comm]
  rw [← Nat.cast_lt (α := Rat)]; rw [Nat.cast_mul]; rw [Nat.cast_two]
  -- passing between ℕ- and ℚ-inequalities is annoying, here and above
  nlinarith

中文:
引理 weak_invMulSubgroup_bound
  条件: (h : #(A * A) < (3 / 2 : 有理数) * #A)
  证明: by
  have h₀ : A.Nonempty := nonempty_of_doubling h
  have h₁ a (ha : a in A⁻¹ * A) : (1 / 2 : Rat) * #A < #{xy in A ×ˢ A | xy.1 * xy.2⁻¹ = a} := by
    convert! lt_card_mul_inv_eq (by simpa using Rat.cast_strictMono (K := Real) h) ha
    norm_num
    simp [← Rat.cast_lt (K := Real)]
  have h₂ : forall x in A ×ˢ A, (fun ⟨x, y⟩ => x * y⁻¹) x in A⁻¹ * A := by
    rw [← mul_inv_eq_inv_mul_of_doubling_lt_two (weaken_doubling h)]
    simp only [mem_product, Prod.forall, mem_mul, and_imp, mem_inv]
    intro a b ha hb
    exact ⟨a, ha, b⁻¹, by simp [hb], rfl⟩
  have : ((1 / 2 : Rat) * #A) * #(A⁻¹ * A) < (#A : Rat) ^ 2 := by
    rw [← Nat.cast_pow]; rw [sq]; rw [← card_product]; rw [card_eq_sum_card_fiberwise h₂]; rw [Nat.cast_sum]
    refine (sum_lt_sum_of_nonempty (by simp [h₀]) h₁).trans_eq' ?_
    simp only [sum_const, nsmul_eq_mul, mul_comm]
  rw [← Nat.cast_lt (α := Rat)]; rw [Nat.cast_mul]; rw [Nat.cast_two]
  -- passing between ℕ- and ℚ-inequalities is annoying, here and above
  nlinarith
-/
private lemma weak_invMulSubgroup_bound (h : #(A * A) < (3 / 2 : Rat) * #A) :
    #(A⁻¹ * A) < 2 * #A := by
  have h₀ : A.Nonempty := nonempty_of_doubling h
  have h₁ a (ha : a in A⁻¹ * A) : (1 / 2 : Rat) * #A < #{xy in A ×ˢ A | xy.1 * xy.2⁻¹ = a} := by
    convert! lt_card_mul_inv_eq (by simpa using Rat.cast_strictMono (K := Real) h) ha
    norm_num
    simp [← Rat.cast_lt (K := Real)]
  have h₂ : forall x in A ×ˢ A, (fun ⟨x, y⟩ => x * y⁻¹) x in A⁻¹ * A := by
    rw [← mul_inv_eq_inv_mul_of_doubling_lt_two (weaken_doubling h)]
    simp only [mem_product, Prod.forall, mem_mul, and_imp, mem_inv]
    intro a b ha hb
    exact ⟨a, ha, b⁻¹, by simp [hb], rfl⟩
  have : ((1 / 2 : Rat) * #A) * #(A⁻¹ * A) < (#A : Rat) ^ 2 := by
    rw [← Nat.cast_pow]; rw [sq]; rw [← card_product]; rw [card_eq_sum_card_fiberwise h₂]; rw [Nat.cast_sum]
    refine (sum_lt_sum_of_nonempty (by simp [h₀]) h₁).trans_eq' ?_
    simp only [sum_const, nsmul_eq_mul, mul_comm]
  rw [← Nat.cast_lt (α := Rat)]; rw [Nat.cast_mul]; rw [Nat.cast_two]
  -- passing between ℕ- and ℚ-inequalities is annoying, here and above
  nlinarith

/--
lemma `A_subset_aH` / 引理 `A_subset_aH`

English:
lemma A_subset_aH
  given: (a : G) (ha : a in A)
  statement: A subseteq a • (A⁻¹ * A)
  proof: by
  rw [← smul_mul_assoc]
  exact subset_mul_right _ (by simp [← inv_smul_mem_iff, inv_mem_inv ha])

中文:
引理 A_subset_aH
  条件: (a : G) (ha : a in A)
  结论: A subseteq a • (A⁻¹ * A)
  证明: by
  rw [← smul_mul_assoc]
  exact subset_mul_right _ (by simp [← inv_smul_mem_iff, inv_mem_inv ha])
-/
private lemma A_subset_aH (a : G) (ha : a in A) : A subseteq a • (A⁻¹ * A) := by
  rw [← smul_mul_assoc]
  exact subset_mul_right _ (by simp [← inv_smul_mem_iff, inv_mem_inv ha])

/--
lemma `subgroup_strong_bound_left` / 引理 `subgroup_strong_bound_left`

English:
lemma subgroup_strong_bound_left
  given: (h : #(A * A) < (3 / 2 : Rat) * #A) (a : G) (ha : a in A)
  proof: by
  have h₁ : (A⁻¹ * A) * (A⁻¹ * A) = A⁻¹ * A := by
    rw [← coe_inj]; rw [coe_mul]; rw [coe_mul]; rw [← invMulSubgroup_eq_inv_mul _ h]; rw [coe_mul_coe]
  have h₂ : a • op a • (A⁻¹ * A) = (a • (A⁻¹ * A)) * (op a • (A⁻¹ * A)) := by
    rw [mul_smul_comm]; rw [smul_mul_assoc]; rw [h₁]; rw [smul_comm]
  rw [h₂]
  refine mul_subset_mul (A_subset_aH a ha) ?_
  rw [← mul_inv_eq_inv_mul_of_doubling_lt_two (weaken_doubling h)]; rw [← mul_smul_comm]
  exact subset_mul_left _ (by simp [← inv_smul_mem_iff, inv_mem_inv ha])

中文:
引理 subgroup_strong_bound_left
  条件: (h : #(A * A) < (3 / 2 : 有理数) * #A) (a : G) (ha : a in A)
  证明: by
  have h₁ : (A⁻¹ * A) * (A⁻¹ * A) = A⁻¹ * A := by
    rw [← coe_inj]; rw [coe_mul]; rw [coe_mul]; rw [← invMulSubgroup_eq_inv_mul _ h]; rw [coe_mul_coe]
  have h₂ : a • op a • (A⁻¹ * A) = (a • (A⁻¹ * A)) * (op a • (A⁻¹ * A)) := by
    rw [mul_smul_comm]; rw [smul_mul_assoc]; rw [h₁]; rw [smul_comm]
  rw [h₂]
  refine mul_subset_mul (A_subset_aH a ha) ?_
  rw [← mul_inv_eq_inv_mul_of_doubling_lt_two (weaken_doubling h)]; rw [← mul_smul_comm]
  exact subset_mul_left _ (by simp [← inv_smul_mem_iff, inv_mem_inv ha])
-/
private lemma subgroup_strong_bound_left (h : #(A * A) < (3 / 2 : Rat) * #A) (a : G) (ha : a in A) :
    A * A subseteq a • op a • (A⁻¹ * A) := by
  have h₁ : (A⁻¹ * A) * (A⁻¹ * A) = A⁻¹ * A := by
    rw [← coe_inj]; rw [coe_mul]; rw [coe_mul]; rw [← invMulSubgroup_eq_inv_mul _ h]; rw [coe_mul_coe]
  have h₂ : a • op a • (A⁻¹ * A) = (a • (A⁻¹ * A)) * (op a • (A⁻¹ * A)) := by
    rw [mul_smul_comm]; rw [smul_mul_assoc]; rw [h₁]; rw [smul_comm]
  rw [h₂]
  refine mul_subset_mul (A_subset_aH a ha) ?_
  rw [← mul_inv_eq_inv_mul_of_doubling_lt_two (weaken_doubling h)]; rw [← mul_smul_comm]
  exact subset_mul_left _ (by simp [← inv_smul_mem_iff, inv_mem_inv ha])

/--
lemma `subgroup_strong_bound_right` / 引理 `subgroup_strong_bound_right`

English:
lemma subgroup_strong_bound_right
  given: (h : #(A * A) < (3 / 2 : Rat) * #A) (a : G) (ha : a in A)
  proof: by
  intro z hz
  simp only [mem_smul_finset, smul_eq_mul_unop, unop_op, smul_eq_mul, mem_mul, mem_inv,
    exists_exists_and_eq_and] at hz
  obtain ⟨d, ⟨b, hb, c, hc, rfl⟩, hz⟩ := hz
  let l : Finset G := A inter ((z * a⁻¹) • (A⁻¹ * A))
    -- ^ set of x ∈ A st ∃ y ∈ H a with x y = z
  let r : Finset G := (a • (A⁻¹ * A)) inter (z • A⁻¹)
    -- ^ set of x ∈ a H st ∃ y ∈ A with x y = z
  have : (A⁻¹ * A) * (A⁻¹ * A) = A⁻¹ * A := by
    rw [← coe_inj]; rw [coe_mul]; rw [coe_mul]; rw [← invMulSubgroup_eq_inv_mul _ h]; rw [coe_mul_coe]
  have hl : l = A := by
    rw [inter_eq_left]; rw [← this]; rw [subset_smul_finset_iff]
    simp only [← hz, mul_inv_rev, inv_inv, ← mul_assoc]
    refine smul_finset_subset_mul ?_
    simp [mul_mem_mul, ha, hb, hc]
  have hr : r = z • A⁻¹ := by
    rw [inter_eq_right]; rw [← this]; rw [mul_assoc _ A]; rw [← mul_inv_eq_inv_mul_of_doubling_lt_two (weaken_doubling h)]; rw [subset_smul_finset_iff]
    simp only [← mul_assoc, smul_smul]
    refine smul_finset_subset_mul ?_
    simp [← hz, mul_mem_mul, ha, hb, hc]
  have lr : l union r subseteq a • (A⁻¹ * A) := by
    rw [union_subset_iff]; rw [hl]
    exact ⟨A_subset_aH a ha, inter_subset_left⟩
  have : #l = #A := by rw [hl]
  have : #r = #A := by rw [hr, card_smul_finset, card_inv]
  have : #(l union r) < 2 * #A := by
    refine (card_le_card lr).trans_lt ?_
    rw [card_smul_finset]
    exact weak_invMulSubgroup_bound h
  have ⟨t, ht⟩ : (l inter r).Nonempty := by
    rw [← card_pos]
    linarith [card_inter_add_card_union l r]
  simp only [hl, hr, mem_inter, ← inv_smul_mem_iff, smul_eq_mul, mem_inv', mul_inv_rev,
    inv_inv] at ht
  rw [mem_mul]
  exact ⟨t, ht.1, t⁻¹ * z, ht.2, by simp⟩

中文:
引理 subgroup_strong_bound_right
  条件: (h : #(A * A) < (3 / 2 : 有理数) * #A) (a : G) (ha : a in A)
  证明: by
  intro z hz
  simp only [mem_smul_finset, smul_eq_mul_unop, unop_op, smul_eq_mul, mem_mul, mem_inv,
    exists_exists_and_eq_and] at hz
  obtain ⟨d, ⟨b, hb, c, hc, rfl⟩, hz⟩ := hz
  let l : Finset G := A inter ((z * a⁻¹) • (A⁻¹ * A))
    -- ^ set of x ∈ A st ∃ y ∈ H a with x y = z
  let r : Finset G := (a • (A⁻¹ * A)) inter (z • A⁻¹)
    -- ^ set of x ∈ a H st ∃ y ∈ A with x y = z
  have : (A⁻¹ * A) * (A⁻¹ * A) = A⁻¹ * A := by
    rw [← coe_inj]; rw [coe_mul]; rw [coe_mul]; rw [← invMulSubgroup_eq_inv_mul _ h]; rw [coe_mul_coe]
  have hl : l = A := by
    rw [inter_eq_left]; rw [← this]; rw [subset_smul_finset_iff]
    simp only [← hz, mul_inv_rev, inv_inv, ← mul_assoc]
    refine smul_finset_subset_mul ?_
    simp [mul_mem_mul, ha, hb, hc]
  have hr : r = z • A⁻¹ := by
    rw [inter_eq_right]; rw [← this]; rw [mul_assoc _ A]; rw [← mul_inv_eq_inv_mul_of_doubling_lt_two (weaken_doubling h)]; rw [subset_smul_finset_iff]
    simp only [← mul_assoc, smul_smul]
    refine smul_finset_subset_mul ?_
    simp [← hz, mul_mem_mul, ha, hb, hc]
  have lr : l union r subseteq a • (A⁻¹ * A) := by
    rw [union_subset_iff]; rw [hl]
    exact ⟨A_subset_aH a ha, inter_subset_left⟩
  have : #l = #A := by rw [hl]
  have : #r = #A := by rw [hr, card_smul_finset, card_inv]
  have : #(l union r) < 2 * #A := by
    refine (card_le_card lr).trans_lt ?_
    rw [card_smul_finset]
    exact weak_invMulSubgroup_bound h
  have ⟨t, ht⟩ : (l inter r).Nonempty := by
    rw [← card_pos]
    linarith [card_inter_add_card_union l r]
  simp only [hl, hr, mem_inter, ← inv_smul_mem_iff, smul_eq_mul, mem_inv', mul_inv_rev,
    inv_inv] at ht
  rw [mem_mul]
  exact ⟨t, ht.1, t⁻¹ * z, ht.2, by simp⟩
-/
private lemma subgroup_strong_bound_right (h : #(A * A) < (3 / 2 : Rat) * #A) (a : G) (ha : a in A) :
    a • op a • (A⁻¹ * A) subseteq A * A := by
  intro z hz
  simp only [mem_smul_finset, smul_eq_mul_unop, unop_op, smul_eq_mul, mem_mul, mem_inv,
    exists_exists_and_eq_and] at hz
  obtain ⟨d, ⟨b, hb, c, hc, rfl⟩, hz⟩ := hz
  let l : Finset G := A inter ((z * a⁻¹) • (A⁻¹ * A))
    -- ^ set of x ∈ A st ∃ y ∈ H a with x y = z
  let r : Finset G := (a • (A⁻¹ * A)) inter (z • A⁻¹)
    -- ^ set of x ∈ a H st ∃ y ∈ A with x y = z
  have : (A⁻¹ * A) * (A⁻¹ * A) = A⁻¹ * A := by
    rw [← coe_inj]; rw [coe_mul]; rw [coe_mul]; rw [← invMulSubgroup_eq_inv_mul _ h]; rw [coe_mul_coe]
  have hl : l = A := by
    rw [inter_eq_left]; rw [← this]; rw [subset_smul_finset_iff]
    simp only [← hz, mul_inv_rev, inv_inv, ← mul_assoc]
    refine smul_finset_subset_mul ?_
    simp [mul_mem_mul, ha, hb, hc]
  have hr : r = z • A⁻¹ := by
    rw [inter_eq_right]; rw [← this]; rw [mul_assoc _ A]; rw [← mul_inv_eq_inv_mul_of_doubling_lt_two (weaken_doubling h)]; rw [subset_smul_finset_iff]
    simp only [← mul_assoc, smul_smul]
    refine smul_finset_subset_mul ?_
    simp [← hz, mul_mem_mul, ha, hb, hc]
  have lr : l union r subseteq a • (A⁻¹ * A) := by
    rw [union_subset_iff]; rw [hl]
    exact ⟨A_subset_aH a ha, inter_subset_left⟩
  have : #l = #A := by rw [hl]
  have : #r = #A := by rw [hr, card_smul_finset, card_inv]
  have : #(l union r) < 2 * #A := by
    refine (card_le_card lr).trans_lt ?_
    rw [card_smul_finset]
    exact weak_invMulSubgroup_bound h
  have ⟨t, ht⟩ : (l inter r).Nonempty := by
    rw [← card_pos]
    linarith [card_inter_add_card_union l r]
  simp only [hl, hr, mem_inter, ← inv_smul_mem_iff, smul_eq_mul, mem_inv', mul_inv_rev,
    inv_inv] at ht
  rw [mem_mul]
  exact ⟨t, ht.1, t⁻¹ * z, ht.2, by simp⟩

open scoped RightActions in
/--
lemma `smul_inv_mul_opSMul_eq_mul_of_doubling_lt_three_halves` / 引理 `smul_inv_mul_opSMul_eq_mul_of_doubling_lt_three_halves`

English:
lemma smul_inv_mul_opSMul_eq_mul_of_doubling_lt_three_halves
  statement: (h : #(A * A) < (3 / 2 : Rat) * #A)
  proof: (subgroup_strong_bound_right h a ha).antisymm (subgroup_strong_bound_left h a ha)

中文:
引理 smul_inv_mul_opSMul_eq_mul_of_doubling_lt_three_halves
  结论: (h : #(A * A) < (3 / 2 : 有理数) * #A)
  证明: (subgroup_strong_bound_right h a ha).antisymm (subgroup_strong_bound_left h a ha)

Depends on / 依赖: antisymm, subgroup_strong_bound_left, subgroup_strong_bound_right
-/
lemma smul_inv_mul_opSMul_eq_mul_of_doubling_lt_three_halves (h : #(A * A) < (3 / 2 : Rat) * #A)
    (ha : a in A) : a •> ((A⁻¹ * A) <• a) = A * A :=
  (subgroup_strong_bound_right h a ha).antisymm (subgroup_strong_bound_left h a ha)

/--
lemma `card_inv_mul_of_doubling_lt_three_halves` / 引理 `card_inv_mul_of_doubling_lt_three_halves`

English:
lemma card_inv_mul_of_doubling_lt_three_halves
  given: (h : #(A * A) < (3 / 2 : Rat) * #A)
  proof: by
  obtain ⟨a, ha⟩ := nonempty_of_doubling h
  simp_rw [← smul_inv_mul_opSMul_eq_mul_of_doubling_lt_three_halves h ha, card_smul_finset]

中文:
引理 card_inv_mul_of_doubling_lt_three_halves
  条件: (h : #(A * A) < (3 / 2 : 有理数) * #A)
  证明: by
  obtain ⟨a, ha⟩ := nonempty_of_doubling h
  simp_rw [← smul_inv_mul_opSMul_eq_mul_of_doubling_lt_three_halves h ha, card_smul_finset]

Depends on / 依赖: card_smul_finset, nonempty_of_doubling, simp_rw, smul_inv_mul_opSMul_eq_mul_of_doubling_lt_three_halves
-/
lemma card_inv_mul_of_doubling_lt_three_halves (h : #(A * A) < (3 / 2 : Rat) * #A) :
    #(A⁻¹ * A) = #(A * A) := by
  obtain ⟨a, ha⟩ := nonempty_of_doubling h
  simp_rw [← smul_inv_mul_opSMul_eq_mul_of_doubling_lt_three_halves h ha, card_smul_finset]

/--
lemma `smul_inv_mul_eq_inv_mul_opSMul` / 引理 `smul_inv_mul_eq_inv_mul_opSMul`

English:
lemma smul_inv_mul_eq_inv_mul_opSMul
  given: (h : #(A * A) < (3 / 2 : Rat) * #A) (ha : a in A)
  proof: by
  refine subset_antisymm ?_ ?_
  · rw [subset_smul_finset_iff, ← op_inv]
    calc
      a •> (A⁻¹ * A) <• a⁻¹ subseteq a •> (A⁻¹ * A) * A⁻¹ := op_smul_finset_subset_mul (by simpa)
      _ subseteq A * (A⁻¹ * A) * A⁻¹ := by grw [smul_finset_subset_mul (by simpa)]
      _ = A⁻¹ * A := by
        simp_rw [← coe_inj, coe_mul]
        rw [← mul_assoc]; rw [← invMulSubgroup_eq_mul_inv _ h]; rw [mul_assoc]; rw [← invMulSubgroup_eq_mul_inv _ h]; rw [coe_mul_coe]; rw [invMulSubgroup_eq_inv_mul]
  · rw [subset_smul_finset_iff]
    calc
      a⁻¹ •> ((A⁻¹ * A) <• a) subseteq A⁻¹ * (A⁻¹ * A) <• a := smul_finset_subset_mul (by simpa)
      _ subseteq A⁻¹ * ((A⁻¹ * A) * A) := by grw [op_smul_finset_subset_mul (by simpa)]
      _ = A⁻¹ * A := by
        rw [← mul_inv_eq_inv_mul_of_doubling_lt_two <| weaken_doubling h]
        simp_rw [← coe_inj, coe_mul]
        rw [mul_assoc]; rw [← invMulSubgroup_eq_inv_mul _ h]; rw [← mul_assoc]; rw [← invMulSubgroup_eq_inv_mul _ h]; rw [← invMulSubgroup_eq_mul_inv _ h]; rw [coe_mul_coe]

中文:
引理 smul_inv_mul_eq_inv_mul_opSMul
  条件: (h : #(A * A) < (3 / 2 : 有理数) * #A) (ha : a in A)
  证明: by
  refine subset_antisymm ?_ ?_
  · rw [subset_smul_finset_iff, ← op_inv]
    calc
      a •> (A⁻¹ * A) <• a⁻¹ subseteq a •> (A⁻¹ * A) * A⁻¹ := op_smul_finset_subset_mul (by simpa)
      _ subseteq A * (A⁻¹ * A) * A⁻¹ := by grw [smul_finset_subset_mul (by simpa)]
      _ = A⁻¹ * A := by
        simp_rw [← coe_inj, coe_mul]
        rw [← mul_assoc]; rw [← invMulSubgroup_eq_mul_inv _ h]; rw [mul_assoc]; rw [← invMulSubgroup_eq_mul_inv _ h]; rw [coe_mul_coe]; rw [invMulSubgroup_eq_inv_mul]
  · rw [subset_smul_finset_iff]
    calc
      a⁻¹ •> ((A⁻¹ * A) <• a) subseteq A⁻¹ * (A⁻¹ * A) <• a := smul_finset_subset_mul (by simpa)
      _ subseteq A⁻¹ * ((A⁻¹ * A) * A) := by grw [op_smul_finset_subset_mul (by simpa)]
      _ = A⁻¹ * A := by
        rw [← mul_inv_eq_inv_mul_of_doubling_lt_two <| weaken_doubling h]
        simp_rw [← coe_inj, coe_mul]
        rw [mul_assoc]; rw [← invMulSubgroup_eq_inv_mul _ h]; rw [← mul_assoc]; rw [← invMulSubgroup_eq_inv_mul _ h]; rw [← invMulSubgroup_eq_mul_inv _ h]; rw [coe_mul_coe]

Depends on / 依赖: coe_inj, coe_mul, coe_mul_coe, invMulSubgroup_eq_inv_mul, invMulSubgroup_eq_mul_inv, mul_assoc, op_inv, op_smul_finset_subset_mul, simp_rw, smul_finset_subset_mul, subset_antisymm, subset_smul_finset_iff, subseteq
-/
lemma smul_inv_mul_eq_inv_mul_opSMul (h : #(A * A) < (3 / 2 : Rat) * #A) (ha : a in A) :
    a •> (A⁻¹ * A) = (A⁻¹ * A) <• a := by
  refine subset_antisymm ?_ ?_
  · rw [subset_smul_finset_iff, ← op_inv]
    calc
      a •> (A⁻¹ * A) <• a⁻¹ subseteq a •> (A⁻¹ * A) * A⁻¹ := op_smul_finset_subset_mul (by simpa)
      _ subseteq A * (A⁻¹ * A) * A⁻¹ := by grw [smul_finset_subset_mul (by simpa)]
      _ = A⁻¹ * A := by
        simp_rw [← coe_inj, coe_mul]
        rw [← mul_assoc]; rw [← invMulSubgroup_eq_mul_inv _ h]; rw [mul_assoc]; rw [← invMulSubgroup_eq_mul_inv _ h]; rw [coe_mul_coe]; rw [invMulSubgroup_eq_inv_mul]
  · rw [subset_smul_finset_iff]
    calc
      a⁻¹ •> ((A⁻¹ * A) <• a) subseteq A⁻¹ * (A⁻¹ * A) <• a := smul_finset_subset_mul (by simpa)
      _ subseteq A⁻¹ * ((A⁻¹ * A) * A) := by grw [op_smul_finset_subset_mul (by simpa)]
      _ = A⁻¹ * A := by
        rw [← mul_inv_eq_inv_mul_of_doubling_lt_two <| weaken_doubling h]
        simp_rw [← coe_inj, coe_mul]
        rw [mul_assoc]; rw [← invMulSubgroup_eq_inv_mul _ h]; rw [← mul_assoc]; rw [← invMulSubgroup_eq_inv_mul _ h]; rw [← invMulSubgroup_eq_mul_inv _ h]; rw [coe_mul_coe]

open scoped RightActions in
/--
theorem `doubling_lt_three_halves` / 定理 `doubling_lt_three_halves`

English:
theorem doubling_lt_three_halves
  given: (h : #(A * A) < (3 / 2 : Rat) * #A)
  proof: by
  let H := invMulSubgroup A h
  refine ⟨H, inferInstance, ?_, fun a ha => ⟨?_, ?_⟩⟩
  · simp only [invMulSubgroup, ← coe_mul, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
      mem_coe, ← Nat.card_eq_fintype_card, H]
    rwa [Nat.card_eq_finsetCard, card_inv_mul_of_doubling_lt_three_halves h]
  · rw [invMulSubgroup_eq_inv_mul]
    exact_mod_cast A_subset_aH a ha
  · simpa [H, invMulSubgroup_eq_inv_mul, ← coe_inv, ← coe_mul, ← coe_smul_finset]
      using smul_inv_mul_eq_inv_mul_opSMul h ha

中文:
定理 doubling_lt_three_halves
  条件: (h : #(A * A) < (3 / 2 : 有理数) * #A)
  证明: by
  let H := invMulSubgroup A h
  refine ⟨H, inferInstance, ?_, fun a ha => ⟨?_, ?_⟩⟩
  · simp only [invMulSubgroup, ← coe_mul, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
      mem_coe, ← Nat.card_eq_fintype_card, H]
    rwa [Nat.card_eq_finsetCard, card_inv_mul_of_doubling_lt_three_halves h]
  · rw [invMulSubgroup_eq_inv_mul]
    exact_mod_cast A_subset_aH a ha
  · simpa [H, invMulSubgroup_eq_inv_mul, ← coe_inv, ← coe_mul, ← coe_smul_finset]
      using smul_inv_mul_eq_inv_mul_opSMul h ha

Depends on / 依赖: A_subset_aH, Nat.card_eq_finsetCard, Nat.card_eq_fintype_card, Subgroup, Subgroup.mem_mk, Submonoid, Submonoid.mem_mk, Subsemigroup, Subsemigroup.mem_mk, card_eq_finsetCard, card_eq_fintype_card, card_inv_mul_of_doubling_lt_three_halves, coe_inv, coe_mul, coe_smul_finset, invMulSubgroup, invMulSubgroup_eq_inv_mul, mem_coe, mem_mk, smul_inv_mul_eq_inv_mul_opSMul
-/
theorem doubling_lt_three_halves (h : #(A * A) < (3 / 2 : Rat) * #A) :
    exists (H : Subgroup G) (_ : Fintype H), Fintype.card H < (3 / 2 : Rat) * #A ∧ forall a in A,
      (A : Set G) subseteq a • H ∧ a •> (H : Set G) = H <• a := by
  let H := invMulSubgroup A h
  refine ⟨H, inferInstance, ?_, fun a ha => ⟨?_, ?_⟩⟩
  · simp only [invMulSubgroup, ← coe_mul, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
      mem_coe, ← Nat.card_eq_fintype_card, H]
    rwa [Nat.card_eq_finsetCard, card_inv_mul_of_doubling_lt_three_halves h]
  · rw [invMulSubgroup_eq_inv_mul]
    exact_mod_cast A_subset_aH a ha
  · simpa [H, invMulSubgroup_eq_inv_mul, ← coe_inv, ← coe_mul, ← coe_smul_finset]
      using smul_inv_mul_eq_inv_mul_opSMul h ha

/-! ### Doubling strictly less than `φ` -/

omit [DecidableEq G] in
/--
lemma `op_smul_eq_iff_mem` / 引理 `op_smul_eq_iff_mem`

English:
lemma op_smul_eq_iff_mem
  statement: {H : Subgroup G} {c : Set G} {x : G}
  proof: by
  refine ⟨fun hx => ?_, fun hx =>
    by simp only [← hx, mem_rightCoset_iff, mul_inv_cancel, SetLike.mem_coe, one_mem]⟩
  obtain ⟨⟨a⟩, rfl⟩ := hc
  change _ = _ <• _
  rw [eq_comm]; rw [smul_eq_iff_eq_inv_smul]; rw [← op_inv]; rw [op_smul_op_smul]; rw [rightCoset_mem_rightCoset]
  rwa [← op_smul_eq_mul, op_inv, ← SetLike.mem_coe, ← Set.mem_smul_set_iff_inv_smul_mem]

omit [DecidableEq G] in

中文:
引理 op_smul_eq_iff_mem
  结论: {H : 子群 G} {c : 集合 G} {x : G}
  证明: by
  refine ⟨fun hx => ?_, fun hx =>
    by simp only [← hx, mem_rightCoset_iff, mul_inv_cancel, SetLike.mem_coe, one_mem]⟩
  obtain ⟨⟨a⟩, rfl⟩ := hc
  change _ = _ <• _
  rw [eq_comm]; rw [smul_eq_iff_eq_inv_smul]; rw [← op_inv]; rw [op_smul_op_smul]; rw [rightCoset_mem_rightCoset]
  rwa [← op_smul_eq_mul, op_inv, ← SetLike.mem_coe, ← Set.mem_smul_set_iff_inv_smul_mem]

omit [DecidableEq G] in
-/
private lemma op_smul_eq_iff_mem {H : Subgroup G} {c : Set G} {x : G}
    (hc : c in orbit Gᵐᵒᵖ (H : Set G)) : x in c ↔ H <• x = c := by
  refine ⟨fun hx => ?_, fun hx =>
    by simp only [← hx, mem_rightCoset_iff, mul_inv_cancel, SetLike.mem_coe, one_mem]⟩
  obtain ⟨⟨a⟩, rfl⟩ := hc
  change _ = _ <• _
  rw [eq_comm]; rw [smul_eq_iff_eq_inv_smul]; rw [← op_inv]; rw [op_smul_op_smul]; rw [rightCoset_mem_rightCoset]
  rwa [← op_smul_eq_mul, op_inv, ← SetLike.mem_coe, ← Set.mem_smul_set_iff_inv_smul_mem]

omit [DecidableEq G] in
/--
lemma `op_smul_eq_op_smul_iff_mem` / 引理 `op_smul_eq_op_smul_iff_mem`

English:
lemma op_smul_eq_op_smul_iff_mem
  given: {H : Subgroup G} {x y : G}
  proof: op_smul_eq_iff_mem (mem_orbit _ _)

omit [DecidableEq G] in

中文:
引理 op_smul_eq_op_smul_iff_mem
  条件: {H : 子群 G} {x y : G}
  证明: op_smul_eq_iff_mem (mem_orbit _ _)

omit [DecidableEq G] in
-/
private lemma op_smul_eq_op_smul_iff_mem {H : Subgroup G} {x y : G} :
    x in (H : Set G) <• y ↔ (H : Set G) <• x = H <• y := op_smul_eq_iff_mem (mem_orbit _ _)

omit [DecidableEq G] in
/--
lemma `exists_subset_mul_eq_mul_injOn` / 引理 `exists_subset_mul_eq_mul_injOn`

English:
lemma exists_subset_mul_eq_mul_injOn
  given: (H : Subgroup G) (A : Finset G)
  proof: by
  obtain ⟨Z, hZA, hZinj, hHZA⟩ :=
    ((A : Set G).surjOn_image ((H : Set G) <• ·)).exists_subset_injOn_image_eq
  lift Z to Finset G using A.finite_toSet.subset hZA
  refine ⟨Z, mod_cast hZA, ?_, hZinj⟩
  simpa [-SetLike.mem_coe, Set.iUnion_op_smul_set] using congr(Set.sUnion $hHZA)

中文:
引理 存在_subset_mul_eq_mul_injOn
  条件: (H : 子群 G) (A : 有限集 G)
  证明: by
  obtain ⟨Z, hZA, hZinj, hHZA⟩ :=
    ((A : Set G).surjOn_image ((H : Set G) <• ·)).exists_subset_injOn_image_eq
  lift Z to Finset G using A.finite_toSet.subset hZA
  refine ⟨Z, mod_cast hZA, ?_, hZinj⟩
  simpa [-SetLike.mem_coe, Set.iUnion_op_smul_set] using congr(Set.sUnion $hHZA)
-/
private lemma exists_subset_mul_eq_mul_injOn (H : Subgroup G) (A : Finset G) :
    exists Z subseteq A, (H : Set G) * Z = H * A ∧ (Z : Set G).InjOn ((H : Set G) <• ·) := by
  obtain ⟨Z, hZA, hZinj, hHZA⟩ :=
    ((A : Set G).surjOn_image ((H : Set G) <• ·)).exists_subset_injOn_image_eq
  lift Z to Finset G using A.finite_toSet.subset hZA
  refine ⟨Z, mod_cast hZA, ?_, hZinj⟩
  simpa [-SetLike.mem_coe, Set.iUnion_op_smul_set] using congr(Set.sUnion $hHZA)

/--
lemma `card_mul_eq_mul_card_of_injOn_opSMul` / 引理 `card_mul_eq_mul_card_of_injOn_opSMul`

English:
lemma card_mul_eq_mul_card_of_injOn_opSMul
  statement: {H : Subgroup G} [Fintype H]
  proof: by
  rw [card_mul_iff.2]
  · simp
  rintro ⟨h₁, z₁⟩ ⟨hh₁, hz₁⟩ ⟨h₂, z₂⟩ ⟨hh₂, hz₂⟩ h
  simp only [Set.coe_toFinset, SetLike.mem_coe] at *
obtain rfl := hZ hz₁ hz₂ (rightCoset_eq_iff _).2 by
    simpa [eq_inv_mul_iff_mul_eq.2 h, mul_assoc] using mul_mem (inv_mem hh₂) hh₁
  simp_all

中文:
引理 card_mul_eq_mul_card_of_injOn_opSMul
  结论: {H : 子群 G} [有限类型 H]
  证明: by
  rw [card_mul_iff.2]
  · simp
  rintro ⟨h₁, z₁⟩ ⟨hh₁, hz₁⟩ ⟨h₂, z₂⟩ ⟨hh₂, hz₂⟩ h
  simp only [Set.coe_toFinset, SetLike.mem_coe] at *
obtain rfl := hZ hz₁ hz₂ (rightCoset_eq_iff _).2 by
    simpa [eq_inv_mul_iff_mul_eq.2 h, mul_assoc] using mul_mem (inv_mem hh₂) hh₁
  simp_all
-/
private lemma card_mul_eq_mul_card_of_injOn_opSMul {H : Subgroup G} [Fintype H]
    {Z : Finset G} (hZ : (Z : Set G).InjOn ((H : Set G) <• ·)) :
    Fintype.card H * #Z = #(Set.toFinset H * Z) := by
  rw [card_mul_iff.2]
  · simp
  rintro ⟨h₁, z₁⟩ ⟨hh₁, hz₁⟩ ⟨h₂, z₂⟩ ⟨hh₂, hz₂⟩ h
  simp only [Set.coe_toFinset, SetLike.mem_coe] at *
obtain rfl := hZ hz₁ hz₂ (rightCoset_eq_iff _).2 by
    simpa [eq_inv_mul_iff_mul_eq.2 h, mul_assoc] using mul_mem (inv_mem hh₂) hh₁
  simp_all

set_option linter.flexible false in -- simp followed by positivity
open goldenRatio in
/--
theorem `doubling_lt_golden_ratio` / 定理 `doubling_lt_golden_ratio`

English:
theorem doubling_lt_golden_ratio
  statement: (hK₁ : 1 < K) (hKφ : K < φ)
  proof: by
  -- Some useful initial calculations
  have K_pos : 0 < K := by positivity
  have hK₀ : 0 < K := by positivity
  have hKφ' : 0 < φ - K := by linarith
  have hKψ' : 0 < K - ψ := by linarith [Real.goldenConj_neg]
  have hK₂' : 0 < 2 - K := by linarith [Real.goldenRatio_lt_two]
  have const_pos : 0 < K * (2 - K) / ((φ - K) * (K - ψ)) := by positivity
  -- We dispatch the trivial case `A = ∅` separately.
  obtain rfl | A_nonempty := A.eq_empty_or_nonempty
  · exact ⟨⊥, inferInstance, ∅, by simp; positivity⟩
  -- In the case where `A` is non-empty, we consider the set `S := A * A⁻¹` and its stabilizer `H`.
  let S := A * A⁻¹
  let H := stabilizer G S
  -- `S` is finite and non-empty (because `A` is), and therefore `H` is finite too.
  have S_nonempty : S.Nonempty := by simpa [S]
  have : Finite H := by simpa [H] using! stabilizer_finite (by simpa) S.finite_toSet
  cases nonempty_fintype H
  -- By definition, `H * S = S`.
  have H_mul_S : (H : Set G) * S = S := by simp [H, ← stabilizer_coe_finset]
  -- Since `H` is a subgroup, find a finite set `Z ⊆ S` such that `H * Z = S` and `|H| * |Z| = |S|`.
  obtain ⟨Z, hZ⟩ := exists_subset_mul_eq_mul_injOn H S
  have H_mul_Z : (H : Set G) * Z = S := by simp [hZ.2.1, H_mul_S]
  have H_toFinset_mul_Z : Set.toFinset H * Z = S := by simpa [← Finset.coe_inj]
  have card_H_mul_card_Z : Fintype.card H * #Z = #S := by
    simpa [card_mul_eq_mul_card_of_injOn_opSMul hZ.2.2] using! congr_arg _ H_toFinset_mul_Z
  -- It remains to show that `|Z| ≤ C(K)` for some `C(K)` depending only on `K`.
  refine ⟨H, inferInstance, Z, ?_, mod_cast H_mul_Z⟩
  -- This is equivalent to showing that `|H| ≥ c(K)|S|` for some `c(K)` depending only on `K`.
  suffices ((φ - K) * (K - ψ)) / ((2 - K) * K) * #S <= Fintype.card H by
    calc
          (#Z : Real)
      _ = (Fintype.card H / #S : Real)⁻¹ := by simp [← card_H_mul_card_Z]
      _ <= (((φ - K) * (K - ψ) / ((2 - K) * K) * #S) / #S)⁻¹ := by gcongr
      _ = (2 - K) * K / ((φ - K) * (K - ψ)) := by
        have : (#S : Real) != 0 := by positivity
        simp [this]
  -- Write `r(z)` the number of representations of `z ∈ S` as `x * y⁻¹` for `x, y ∈ A`.
  let r z : Nat := A.convolution A⁻¹ z
  -- `r` is invariant under inverses.
  have r_inv z : r z⁻¹ = r z := by simp [r, inv_inv]
  -- We show that every `z ∈ S` with at least `(K - 1)|A|` representations lies in `H`,
  -- and that such `z` make up a proportion of at least `(2 - K) / ((φ - K) * (K - ψ))` of `S`.
  calc
        (φ - K) * (K - ψ) / ((2 - K) * K) * #S
    _ <= #{z in S | (K - 1) * #A < r z} := ?_
    _ <= #(H : Set G).toFinset := ?_
    _ = Fintype.card H := by simp
  -- First, let's show that a large proportion of all `z ∈ S` have many representations.
  · -- Let `l` be that number.
    set l : Nat := #{z in S | (K - 1) * #A < r z} with hk
    -- By upper-bounding `r(z)` by `(K - 1)|A|` for the `z` with few representations,
    -- and by `|A|` for the `z` with many representations,
    -- we get `|A|² ≤ l|A| + (|S| - l)(K - 1)|A| = ((2 - K)l + (K - 1)|S|)|A|`.
    have ineq : #A * #A <= ((2 - K) * l + (K - 1) * #S) * #A := by
      calc
            (#A : Real) * #A
        _ = #A * #A⁻¹ := by simp
        _ = #(A ×ˢ A⁻¹) := by simp
        _ = ∑ z in S, ↑(r z) := by
          norm_cast
          exact card_eq_sum_card_fiberwise fun xy hxy =>
            mul_mem_mul (mem_product.mp hxy).1 (mem_product.mp hxy).2
        _ = ∑ z in S with (K - 1) * #A < r z, ↑(r z) + ∑ z in S with r z <= (K - 1) * #A, ↑(r z) := by
          norm_cast; simp_rw [← not_lt, sum_filter_add_sum_filter_not]
        _ <= ∑ z in S with (K - 1) * #A < r z, ↑(#A)
          + ∑ z in S with r z <= (K - 1) * #A, (K - 1) * #A := by
          gcongr with z hz z hz
          · exact convolution_le_card_left
          · simp_all
        _ = l * #A + (#S - l) * (K - 1) * #A := by
          simp [hk, ← not_lt, mul_assoc,
            ← S.card_filter_add_card_filter_not fun z => (K - 1) * #A < r z]
        _ = ((2 - K) * l + (K - 1) * #S) * #A := by ring
    -- By cancelling `|A|` on both sides, we get `|A| ≤ (2 - K)l + (K - 1)|S|`.
    -- By composing with `|S| ≤ K|A|`, we get `|S| ≤ (2 - K)Kl + (K - 1)K|S|`.
    have : 0 < #A := by positivity
    replace ineq := calc
          (#S : Real)
      _ <= K * #A := ‹_›
      _ <= K * ((2 - K) * l + (K - 1) * #S) := by
gcongr; exact le_of_mul_le_mul_right ineq by positivity
      _ = (2 - K) * K * l + (K - 1) * K * #S := by ring
    -- Now, we are done.
    calc
          (φ - K) * (K - ψ) / ((2 - K) * K) * #S
      _ = (φ - K) * (K - ψ) * #S / ((2 - K) * K) := div_mul_eq_mul_div ..
      _ <= (2 - K) * K * l / ((2 - K) * K) := by
        have := Real.goldenRatio_mul_goldenConj
        have := Real.goldenRatio_add_goldenConj
        rw [show (φ - K) * (K - ψ) = 1 - (K - 1) * K by grind]
        gcongr ?_ / _
        linarith [ineq]
      _ = l := by field
  -- Second, let's show that the `z ∈ S` with many representations are in `H`.
  · gcongr
    simp only [subset_iff, mem_filter, Set.mem_toFinset, SetLike.mem_coe, and_imp]
    rintro z hz hrz
    -- It's enough to show that `z * w ∈ S` for all `w ∈ S`.
    rw [mem_stabilizer_finset']
    rintro w hw
    -- Since `w ∈ S` and `|A⁻¹ * A| ≤ K|A|`, we know that `r(w) ≥ (2 - K)|A|`.
    have hrw : (2 - K) * #A <= r w := by
      simpa [card_mul_inv_eq_convolution_inv] using! le_card_mul_inv_eq hA₁ (by simpa)
    -- But also `r(z⁻¹) = r(z) > (K - 1)|A|`.
    rw [← r_inv] at hrz
    simp only [r, ← card_inter_smul] at hrz hrw
    -- By inclusion-exclusion, we get that `(z⁻¹ •> A) ∩ (w •> A)` is non-empty.
    have : (0 : Real) < #((z⁻¹ •> A) inter (w •> A)) := by
      have : (#((A inter z⁻¹ •> A) inter (A inter w •> A)) : Real) <= #(z⁻¹ •> A inter w •> A) := by
        gcongr <;> exact inter_subset_right
      have : (#((A inter z⁻¹ •> A) union (A inter w •> A)) : Real) <= #A := by
        gcongr; exact union_subset inter_subset_left inter_subset_left
      have :
          (#((A inter z⁻¹ •> A) inter (A inter w •> A)) + #((A inter z⁻¹ •> A) union (A inter w •> A)) : Real) =
            #(A inter z⁻¹ •> A) + #(A inter w •> A) := mod_cast card_inter_add_card_union ..
      linarith
    -- This is exactly what we set out to prove.
    simpa [S, card_smul_inter_smul, Finset.Nonempty, mem_mul, mem_inv, -mem_inv', and_assoc]
      using! this

中文:
定理 doubling_lt_golden_ratio
  结论: (hK₁ : 1 < K) (hKφ : K < φ)
  证明: by
  -- Some useful initial calculations
  have K_pos : 0 < K := by positivity
  have hK₀ : 0 < K := by positivity
  have hKφ' : 0 < φ - K := by linarith
  have hKψ' : 0 < K - ψ := by linarith [Real.goldenConj_neg]
  have hK₂' : 0 < 2 - K := by linarith [Real.goldenRatio_lt_two]
  have const_pos : 0 < K * (2 - K) / ((φ - K) * (K - ψ)) := by positivity
  -- We dispatch the trivial case `A = ∅` separately.
  obtain rfl | A_nonempty := A.eq_empty_or_nonempty
  · exact ⟨⊥, inferInstance, ∅, by simp; positivity⟩
  -- In the case where `A` is non-empty, we consider the set `S := A * A⁻¹` and its stabilizer `H`.
  let S := A * A⁻¹
  let H := stabilizer G S
  -- `S` is finite and non-empty (because `A` is), and therefore `H` is finite too.
  have S_nonempty : S.Nonempty := by simpa [S]
  have : Finite H := by simpa [H] using! stabilizer_finite (by simpa) S.finite_toSet
  cases nonempty_fintype H
  -- By definition, `H * S = S`.
  have H_mul_S : (H : Set G) * S = S := by simp [H, ← stabilizer_coe_finset]
  -- Since `H` is a subgroup, find a finite set `Z ⊆ S` such that `H * Z = S` and `|H| * |Z| = |S|`.
  obtain ⟨Z, hZ⟩ := exists_subset_mul_eq_mul_injOn H S
  have H_mul_Z : (H : Set G) * Z = S := by simp [hZ.2.1, H_mul_S]
  have H_toFinset_mul_Z : Set.toFinset H * Z = S := by simpa [← Finset.coe_inj]
  have card_H_mul_card_Z : Fintype.card H * #Z = #S := by
    simpa [card_mul_eq_mul_card_of_injOn_opSMul hZ.2.2] using! congr_arg _ H_toFinset_mul_Z
  -- It remains to show that `|Z| ≤ C(K)` for some `C(K)` depending only on `K`.
  refine ⟨H, inferInstance, Z, ?_, mod_cast H_mul_Z⟩
  -- This is equivalent to showing that `|H| ≥ c(K)|S|` for some `c(K)` depending only on `K`.
  suffices ((φ - K) * (K - ψ)) / ((2 - K) * K) * #S <= Fintype.card H by
    calc
          (#Z : Real)
      _ = (Fintype.card H / #S : Real)⁻¹ := by simp [← card_H_mul_card_Z]
      _ <= (((φ - K) * (K - ψ) / ((2 - K) * K) * #S) / #S)⁻¹ := by gcongr
      _ = (2 - K) * K / ((φ - K) * (K - ψ)) := by
        have : (#S : Real) != 0 := by positivity
        simp [this]
  -- Write `r(z)` the number of representations of `z ∈ S` as `x * y⁻¹` for `x, y ∈ A`.
  let r z : Nat := A.convolution A⁻¹ z
  -- `r` is invariant under inverses.
  have r_inv z : r z⁻¹ = r z := by simp [r, inv_inv]
  -- We show that every `z ∈ S` with at least `(K - 1)|A|` representations lies in `H`,
  -- and that such `z` make up a proportion of at least `(2 - K) / ((φ - K) * (K - ψ))` of `S`.
  calc
        (φ - K) * (K - ψ) / ((2 - K) * K) * #S
    _ <= #{z in S | (K - 1) * #A < r z} := ?_
    _ <= #(H : Set G).toFinset := ?_
    _ = Fintype.card H := by simp
  -- First, let's show that a large proportion of all `z ∈ S` have many representations.
  · -- Let `l` be that number.
    set l : Nat := #{z in S | (K - 1) * #A < r z} with hk
    -- By upper-bounding `r(z)` by `(K - 1)|A|` for the `z` with few representations,
    -- and by `|A|` for the `z` with many representations,
    -- we get `|A|² ≤ l|A| + (|S| - l)(K - 1)|A| = ((2 - K)l + (K - 1)|S|)|A|`.
    have ineq : #A * #A <= ((2 - K) * l + (K - 1) * #S) * #A := by
      calc
            (#A : Real) * #A
        _ = #A * #A⁻¹ := by simp
        _ = #(A ×ˢ A⁻¹) := by simp
        _ = ∑ z in S, ↑(r z) := by
          norm_cast
          exact card_eq_sum_card_fiberwise fun xy hxy =>
            mul_mem_mul (mem_product.mp hxy).1 (mem_product.mp hxy).2
        _ = ∑ z in S with (K - 1) * #A < r z, ↑(r z) + ∑ z in S with r z <= (K - 1) * #A, ↑(r z) := by
          norm_cast; simp_rw [← not_lt, sum_filter_add_sum_filter_not]
        _ <= ∑ z in S with (K - 1) * #A < r z, ↑(#A)
          + ∑ z in S with r z <= (K - 1) * #A, (K - 1) * #A := by
          gcongr with z hz z hz
          · exact convolution_le_card_left
          · simp_all
        _ = l * #A + (#S - l) * (K - 1) * #A := by
          simp [hk, ← not_lt, mul_assoc,
            ← S.card_filter_add_card_filter_not fun z => (K - 1) * #A < r z]
        _ = ((2 - K) * l + (K - 1) * #S) * #A := by ring
    -- By cancelling `|A|` on both sides, we get `|A| ≤ (2 - K)l + (K - 1)|S|`.
    -- By composing with `|S| ≤ K|A|`, we get `|S| ≤ (2 - K)Kl + (K - 1)K|S|`.
    have : 0 < #A := by positivity
    replace ineq := calc
          (#S : Real)
      _ <= K * #A := ‹_›
      _ <= K * ((2 - K) * l + (K - 1) * #S) := by
gcongr; exact le_of_mul_le_mul_right ineq by positivity
      _ = (2 - K) * K * l + (K - 1) * K * #S := by ring
    -- Now, we are done.
    calc
          (φ - K) * (K - ψ) / ((2 - K) * K) * #S
      _ = (φ - K) * (K - ψ) * #S / ((2 - K) * K) := div_mul_eq_mul_div ..
      _ <= (2 - K) * K * l / ((2 - K) * K) := by
        have := Real.goldenRatio_mul_goldenConj
        have := Real.goldenRatio_add_goldenConj
        rw [show (φ - K) * (K - ψ) = 1 - (K - 1) * K by grind]
        gcongr ?_ / _
        linarith [ineq]
      _ = l := by field
  -- Second, let's show that the `z ∈ S` with many representations are in `H`.
  · gcongr
    simp only [subset_iff, mem_filter, Set.mem_toFinset, SetLike.mem_coe, and_imp]
    rintro z hz hrz
    -- It's enough to show that `z * w ∈ S` for all `w ∈ S`.
    rw [mem_stabilizer_finset']
    rintro w hw
    -- Since `w ∈ S` and `|A⁻¹ * A| ≤ K|A|`, we know that `r(w) ≥ (2 - K)|A|`.
    have hrw : (2 - K) * #A <= r w := by
      simpa [card_mul_inv_eq_convolution_inv] using! le_card_mul_inv_eq hA₁ (by simpa)
    -- But also `r(z⁻¹) = r(z) > (K - 1)|A|`.
    rw [← r_inv] at hrz
    simp only [r, ← card_inter_smul] at hrz hrw
    -- By inclusion-exclusion, we get that `(z⁻¹ •> A) ∩ (w •> A)` is non-empty.
    have : (0 : Real) < #((z⁻¹ •> A) inter (w •> A)) := by
      have : (#((A inter z⁻¹ •> A) inter (A inter w •> A)) : Real) <= #(z⁻¹ •> A inter w •> A) := by
        gcongr <;> exact inter_subset_right
      have : (#((A inter z⁻¹ •> A) union (A inter w •> A)) : Real) <= #A := by
        gcongr; exact union_subset inter_subset_left inter_subset_left
      have :
          (#((A inter z⁻¹ •> A) inter (A inter w •> A)) + #((A inter z⁻¹ •> A) union (A inter w •> A)) : Real) =
            #(A inter z⁻¹ •> A) + #(A inter w •> A) := mod_cast card_inter_add_card_union ..
      linarith
    -- This is exactly what we set out to prove.
    simpa [S, card_smul_inter_smul, Finset.Nonempty, mem_mul, mem_inv, -mem_inv', and_assoc]
      using! this
-/
theorem doubling_lt_golden_ratio (hK₁ : 1 < K) (hKφ : K < φ)
    (hA₁ : #(A⁻¹ * A) <= K * #A) (hA₂ : #(A * A⁻¹) <= K * #A) :
    exists (H : Subgroup G) (_ : Fintype H) (Z : Finset G),
      #Z <= (2 - K) * K / ((φ - K) * (K - ψ)) ∧ (H : Set G) * Z = A * A⁻¹ := by
  -- Some useful initial calculations
  have K_pos : 0 < K := by positivity
  have hK₀ : 0 < K := by positivity
  have hKφ' : 0 < φ - K := by linarith
  have hKψ' : 0 < K - ψ := by linarith [Real.goldenConj_neg]
  have hK₂' : 0 < 2 - K := by linarith [Real.goldenRatio_lt_two]
  have const_pos : 0 < K * (2 - K) / ((φ - K) * (K - ψ)) := by positivity
  -- We dispatch the trivial case `A = ∅` separately.
  obtain rfl | A_nonempty := A.eq_empty_or_nonempty
  · exact ⟨⊥, inferInstance, ∅, by simp; positivity⟩
  -- In the case where `A` is non-empty, we consider the set `S := A * A⁻¹` and its stabilizer `H`.
  let S := A * A⁻¹
  let H := stabilizer G S
  -- `S` is finite and non-empty (because `A` is), and therefore `H` is finite too.
  have S_nonempty : S.Nonempty := by simpa [S]
  have : Finite H := by simpa [H] using! stabilizer_finite (by simpa) S.finite_toSet
  cases nonempty_fintype H
  -- By definition, `H * S = S`.
  have H_mul_S : (H : Set G) * S = S := by simp [H, ← stabilizer_coe_finset]
  -- Since `H` is a subgroup, find a finite set `Z ⊆ S` such that `H * Z = S` and `|H| * |Z| = |S|`.
  obtain ⟨Z, hZ⟩ := exists_subset_mul_eq_mul_injOn H S
  have H_mul_Z : (H : Set G) * Z = S := by simp [hZ.2.1, H_mul_S]
  have H_toFinset_mul_Z : Set.toFinset H * Z = S := by simpa [← Finset.coe_inj]
  have card_H_mul_card_Z : Fintype.card H * #Z = #S := by
    simpa [card_mul_eq_mul_card_of_injOn_opSMul hZ.2.2] using! congr_arg _ H_toFinset_mul_Z
  -- It remains to show that `|Z| ≤ C(K)` for some `C(K)` depending only on `K`.
  refine ⟨H, inferInstance, Z, ?_, mod_cast H_mul_Z⟩
  -- This is equivalent to showing that `|H| ≥ c(K)|S|` for some `c(K)` depending only on `K`.
  suffices ((φ - K) * (K - ψ)) / ((2 - K) * K) * #S <= Fintype.card H by
    calc
          (#Z : Real)
      _ = (Fintype.card H / #S : Real)⁻¹ := by simp [← card_H_mul_card_Z]
      _ <= (((φ - K) * (K - ψ) / ((2 - K) * K) * #S) / #S)⁻¹ := by gcongr
      _ = (2 - K) * K / ((φ - K) * (K - ψ)) := by
        have : (#S : Real) != 0 := by positivity
        simp [this]
  -- Write `r(z)` the number of representations of `z ∈ S` as `x * y⁻¹` for `x, y ∈ A`.
  let r z : Nat := A.convolution A⁻¹ z
  -- `r` is invariant under inverses.
  have r_inv z : r z⁻¹ = r z := by simp [r, inv_inv]
  -- We show that every `z ∈ S` with at least `(K - 1)|A|` representations lies in `H`,
  -- and that such `z` make up a proportion of at least `(2 - K) / ((φ - K) * (K - ψ))` of `S`.
  calc
        (φ - K) * (K - ψ) / ((2 - K) * K) * #S
    _ <= #{z in S | (K - 1) * #A < r z} := ?_
    _ <= #(H : Set G).toFinset := ?_
    _ = Fintype.card H := by simp
  -- First, let's show that a large proportion of all `z ∈ S` have many representations.
  · -- Let `l` be that number.
    set l : Nat := #{z in S | (K - 1) * #A < r z} with hk
    -- By upper-bounding `r(z)` by `(K - 1)|A|` for the `z` with few representations,
    -- and by `|A|` for the `z` with many representations,
    -- we get `|A|² ≤ l|A| + (|S| - l)(K - 1)|A| = ((2 - K)l + (K - 1)|S|)|A|`.
    have ineq : #A * #A <= ((2 - K) * l + (K - 1) * #S) * #A := by
      calc
            (#A : Real) * #A
        _ = #A * #A⁻¹ := by simp
        _ = #(A ×ˢ A⁻¹) := by simp
        _ = ∑ z in S, ↑(r z) := by
          norm_cast
          exact card_eq_sum_card_fiberwise fun xy hxy =>
            mul_mem_mul (mem_product.mp hxy).1 (mem_product.mp hxy).2
        _ = ∑ z in S with (K - 1) * #A < r z, ↑(r z) + ∑ z in S with r z <= (K - 1) * #A, ↑(r z) := by
          norm_cast; simp_rw [← not_lt, sum_filter_add_sum_filter_not]
        _ <= ∑ z in S with (K - 1) * #A < r z, ↑(#A)
          + ∑ z in S with r z <= (K - 1) * #A, (K - 1) * #A := by
          gcongr with z hz z hz
          · exact convolution_le_card_left
          · simp_all
        _ = l * #A + (#S - l) * (K - 1) * #A := by
          simp [hk, ← not_lt, mul_assoc,
            ← S.card_filter_add_card_filter_not fun z => (K - 1) * #A < r z]
        _ = ((2 - K) * l + (K - 1) * #S) * #A := by ring
    -- By cancelling `|A|` on both sides, we get `|A| ≤ (2 - K)l + (K - 1)|S|`.
    -- By composing with `|S| ≤ K|A|`, we get `|S| ≤ (2 - K)Kl + (K - 1)K|S|`.
    have : 0 < #A := by positivity
    replace ineq := calc
          (#S : Real)
      _ <= K * #A := ‹_›
      _ <= K * ((2 - K) * l + (K - 1) * #S) := by
gcongr; exact le_of_mul_le_mul_right ineq by positivity
      _ = (2 - K) * K * l + (K - 1) * K * #S := by ring
    -- Now, we are done.
    calc
          (φ - K) * (K - ψ) / ((2 - K) * K) * #S
      _ = (φ - K) * (K - ψ) * #S / ((2 - K) * K) := div_mul_eq_mul_div ..
      _ <= (2 - K) * K * l / ((2 - K) * K) := by
        have := Real.goldenRatio_mul_goldenConj
        have := Real.goldenRatio_add_goldenConj
        rw [show (φ - K) * (K - ψ) = 1 - (K - 1) * K by grind]
        gcongr ?_ / _
        linarith [ineq]
      _ = l := by field
  -- Second, let's show that the `z ∈ S` with many representations are in `H`.
  · gcongr
    simp only [subset_iff, mem_filter, Set.mem_toFinset, SetLike.mem_coe, and_imp]
    rintro z hz hrz
    -- It's enough to show that `z * w ∈ S` for all `w ∈ S`.
    rw [mem_stabilizer_finset']
    rintro w hw
    -- Since `w ∈ S` and `|A⁻¹ * A| ≤ K|A|`, we know that `r(w) ≥ (2 - K)|A|`.
    have hrw : (2 - K) * #A <= r w := by
      simpa [card_mul_inv_eq_convolution_inv] using! le_card_mul_inv_eq hA₁ (by simpa)
    -- But also `r(z⁻¹) = r(z) > (K - 1)|A|`.
    rw [← r_inv] at hrz
    simp only [r, ← card_inter_smul] at hrz hrw
    -- By inclusion-exclusion, we get that `(z⁻¹ •> A) ∩ (w •> A)` is non-empty.
    have : (0 : Real) < #((z⁻¹ •> A) inter (w •> A)) := by
      have : (#((A inter z⁻¹ •> A) inter (A inter w •> A)) : Real) <= #(z⁻¹ •> A inter w •> A) := by
        gcongr <;> exact inter_subset_right
      have : (#((A inter z⁻¹ •> A) union (A inter w •> A)) : Real) <= #A := by
        gcongr; exact union_subset inter_subset_left inter_subset_left
      have :
          (#((A inter z⁻¹ •> A) inter (A inter w •> A)) + #((A inter z⁻¹ •> A) union (A inter w •> A)) : Real) =
            #(A inter z⁻¹ •> A) + #(A inter w •> A) := mod_cast card_inter_add_card_union ..
      linarith
    -- This is exactly what we set out to prove.
    simpa [S, card_smul_inter_smul, Finset.Nonempty, mem_mul, mem_inv, -mem_inv', and_assoc]
      using! this

/-! ### Doubling less than `2-ε` -/

variable (ε : Real)

/--
Definition of `expansion` / `expansion` 的定义

English:
definition expansion
  signature: (K : Real) (S A : Finset G)
  body: #(A * S) - K * #A

中文:
定义 expansion
  签名: (K : 实数) (S A : 有限集 G)
  定义体: #(A * S) - K * #A
-/
private def expansion (K : Real) (S A : Finset G) : Real := #(A * S) - K * #A

/--
lemma `expansion_empty` / 引理 `expansion_empty`

English:
lemma expansion_empty
  given: (K : Real) (S : Finset G)
  statement: expansion K S ∅ = 0
  proof: by
  simp [expansion]

中文:
引理 expansion_empty
  条件: (K : 实数) (S : 有限集 G)
  结论: expansion K S ∅ = 0
  证明: by
  simp [expansion]
-/
@[simp] private lemma expansion_empty (K : Real) (S : Finset G) : expansion K S ∅ = 0 := by
  simp [expansion]

/--
lemma `mul_card_le_expansion` / 引理 `mul_card_le_expansion`

English:
lemma mul_card_le_expansion
  given: (hS : S.Nonempty)
  statement: (1 - K) * #A <= expansion K S A
  proof: by
  rw [one_sub_mul]; rw [expansion]; have := card_le_card_mul_right hS (s := A); gcongr

中文:
引理 mul_card_le_expansion
  条件: (hS : S.非空)
  结论: (1 - K) * #A <= expansion K S A
  证明: by
  rw [one_sub_mul]; rw [expansion]; have := card_le_card_mul_right hS (s := A); gcongr
-/
private lemma mul_card_le_expansion (hS : S.Nonempty) : (1 - K) * #A <= expansion K S A := by
  rw [one_sub_mul]; rw [expansion]; have := card_le_card_mul_right hS (s := A); gcongr

/--
lemma `expansion_nonneg` / 引理 `expansion_nonneg`

English:
lemma expansion_nonneg
  given: (hK : K <= 1) (hS : S.Nonempty)
  statement: 0 <= expansion K S A
  proof: by
  nlinarith [mul_card_le_expansion (K := K) hS (A := A)]

中文:
引理 expansion_nonneg
  条件: (hK : K <= 1) (hS : S.非空)
  结论: 0 <= expansion K S A
  证明: by
  nlinarith [mul_card_le_expansion (K := K) hS (A := A)]
-/
@[simp] private lemma expansion_nonneg (hK : K <= 1) (hS : S.Nonempty) : 0 <= expansion K S A := by
  nlinarith [mul_card_le_expansion (K := K) hS (A := A)]

/--
lemma `expansion_pos` / 引理 `expansion_pos`

English:
lemma expansion_pos
  given: (hK : K < 1) (hS : S.Nonempty) (hA : A.Nonempty)
  proof: by
  have : (0 : Real) < #A := by simp [hA]
  nlinarith [mul_card_le_expansion (K := K) hS (A := A)]

中文:
引理 expansion_pos
  条件: (hK : K < 1) (hS : S.非空) (hA : A.非空)
  证明: by
  have : (0 : Real) < #A := by simp [hA]
  nlinarith [mul_card_le_expansion (K := K) hS (A := A)]
-/
@[simp] private lemma expansion_pos (hK : K < 1) (hS : S.Nonempty) (hA : A.Nonempty) :
    0 < expansion K S A := by
  have : (0 : Real) < #A := by simp [hA]
  nlinarith [mul_card_le_expansion (K := K) hS (A := A)]

/--
lemma `expansion_pos_iff` / 引理 `expansion_pos_iff`

English:
lemma expansion_pos_iff
  given: (hK : K < 1) (hS : S.Nonempty)
  proof: by by_contra! rfl; simp at hA
  mpr := expansion_pos hK hS

中文:
引理 expansion_pos_iff
  条件: (hK : K < 1) (hS : S.非空)
  证明: by by_contra! rfl; simp at hA
  mpr := expansion_pos hK hS
-/
@[simp] private lemma expansion_pos_iff (hK : K < 1) (hS : S.Nonempty) :
    0 < expansion K S A ↔ A.Nonempty where
  mp hA := by by_contra! rfl; simp at hA
  mpr := expansion_pos hK hS

/--
lemma `expansion_smul_finset` / 引理 `expansion_smul_finset`

English:
lemma expansion_smul_finset
  given: (K : Real) (S A : Finset G) (a : G)
  proof: by simp [expansion, smul_mul_assoc]

中文:
引理 expansion_smul_finset
  条件: (K : 实数) (S A : 有限集 G) (a : G)
  证明: by simp [expansion, smul_mul_assoc]
-/
@[simp] private lemma expansion_smul_finset (K : Real) (S A : Finset G) (a : G) :
    expansion K S (a • A) = expansion K S A := by simp [expansion, smul_mul_assoc]

/--
lemma `expansion_submodularity` / 引理 `expansion_submodularity`

English:
lemma expansion_submodularity
  proof: by
  have : (#(A inter B) + #(A union B) : Real) = #A + #B := mod_cast card_inter_add_card_union A B
  have : K * #(A inter B) + K * #(A union B) = K * #A + K * #B := by simp only [← mul_add, this]
  have : (#(A * S inter (B * S)) + #(A * S union B * S) : Real) = #(A * S) + #(B * S) :=
    mod_cast card_inter_add_card_union (A * S) (B * S)
  have : (#((A inter B) * S) : Real) <= #(A * S inter (B * S)) := by grw [inter_mul_subset]
  simp_rw [expansion, union_mul]
  nlinarith

中文:
引理 expansion_submodularity
  证明: by
  have : (#(A inter B) + #(A union B) : Real) = #A + #B := mod_cast card_inter_add_card_union A B
  have : K * #(A inter B) + K * #(A union B) = K * #A + K * #B := by simp only [← mul_add, this]
  have : (#(A * S inter (B * S)) + #(A * S union B * S) : Real) = #(A * S) + #(B * S) :=
    mod_cast card_inter_add_card_union (A * S) (B * S)
  have : (#((A inter B) * S) : Real) <= #(A * S inter (B * S)) := by grw [inter_mul_subset]
  simp_rw [expansion, union_mul]
  nlinarith
-/
private lemma expansion_submodularity :
    expansion K S (A inter B) + expansion K S (A union B) <= expansion K S A + expansion K S B := by
  have : (#(A inter B) + #(A union B) : Real) = #A + #B := mod_cast card_inter_add_card_union A B
  have : K * #(A inter B) + K * #(A union B) = K * #A + K * #B := by simp only [← mul_add, this]
  have : (#(A * S inter (B * S)) + #(A * S union B * S) : Real) = #(A * S) + #(B * S) :=
    mod_cast card_inter_add_card_union (A * S) (B * S)
  have : (#((A inter B) * S) : Real) <= #(A * S inter (B * S)) := by grw [inter_mul_subset]
  simp_rw [expansion, union_mul]
  nlinarith

/--
lemma `bddBelow_expansion` / 引理 `bddBelow_expansion`

English:
lemma bddBelow_expansion
  given: (hK : K <= 1) (hS : S.Nonempty)
  proof: ⟨0, by simp [lowerBounds, *]⟩

中文:
引理 bddBelow_expansion
  条件: (hK : K <= 1) (hS : S.非空)
  证明: ⟨0, by simp [lowerBounds, *]⟩
-/
private lemma bddBelow_expansion (hK : K <= 1) (hS : S.Nonempty) :
    BddBelow (Set.range fun A : {A : Finset G // A.Nonempty} => expansion K S A) :=
  ⟨0, by simp [lowerBounds, *]⟩

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def connectivity (K : Real) (S : Finset G)
  body: ⨅ A : {A : Finset G // A.Nonempty}, expansion K S A

中文:
定义 noncomputable
  签名: def connectivity (K : 实数) (S : 有限集 G)
  定义体: ⨅ A : {A : Finset G // A.Nonempty}, expansion K S A
-/
private noncomputable def connectivity (K : Real) (S : Finset G) : Real :=
  ⨅ A : {A : Finset G // A.Nonempty}, expansion K S A

/--
lemma `le_connectivity_iff` / 引理 `le_connectivity_iff`

English:
lemma le_connectivity_iff
  given: (hK : K <= 1) (hS : S.Nonempty) {r : Real}
  proof: by
  have : Nonempty {A : Finset G // A.Nonempty} := ⟨{1}, by simp⟩
  simp [connectivity, le_ciInf_iff, bddBelow_expansion, *]

中文:
引理 le_connectivity_iff
  条件: (hK : K <= 1) (hS : S.非空) {r : 实数}
  证明: by
  have : Nonempty {A : Finset G // A.Nonempty} := ⟨{1}, by simp⟩
  simp [connectivity, le_ciInf_iff, bddBelow_expansion, *]
-/
@[simp] private lemma le_connectivity_iff (hK : K <= 1) (hS : S.Nonempty) {r : Real} :
    r <= connectivity K S ↔ forall ⦃A : Finset G⦄, A.Nonempty -> r <= expansion K S A := by
  have : Nonempty {A : Finset G // A.Nonempty} := ⟨{1}, by simp⟩
  simp [connectivity, le_ciInf_iff, bddBelow_expansion, *]

/--
lemma `connectivity_lt_iff` / 引理 `connectivity_lt_iff`

English:
lemma connectivity_lt_iff
  given: (hK : K <= 1) (hS : S.Nonempty) {r : Real}
  proof: by
  have : Nonempty {A : Finset G // A.Nonempty} := ⟨{1}, by simp⟩
  simp [connectivity, ciInf_lt_iff, bddBelow_expansion, *]

中文:
引理 connectivity_lt_iff
  条件: (hK : K <= 1) (hS : S.非空) {r : 实数}
  证明: by
  have : Nonempty {A : Finset G // A.Nonempty} := ⟨{1}, by simp⟩
  simp [connectivity, ciInf_lt_iff, bddBelow_expansion, *]
-/
@[simp] private lemma connectivity_lt_iff (hK : K <= 1) (hS : S.Nonempty) {r : Real} :
    connectivity K S < r ↔ exists A : Finset G, A.Nonempty ∧ expansion K S A < r := by
  have : Nonempty {A : Finset G // A.Nonempty} := ⟨{1}, by simp⟩
  simp [connectivity, ciInf_lt_iff, bddBelow_expansion, *]

/--
lemma `connectivity_le_expansion` / 引理 `connectivity_le_expansion`

English:
lemma connectivity_le_expansion
  given: (hK : K <= 1) (hS : S.Nonempty) (hA : A.Nonempty)
  proof: (le_connectivity_iff hK hS).1 le_rfl hA

中文:
引理 connectivity_le_expansion
  条件: (hK : K <= 1) (hS : S.非空) (hA : A.非空)
  证明: (le_connectivity_iff hK hS).1 le_rfl hA
-/
@[simp] private lemma connectivity_le_expansion (hK : K <= 1) (hS : S.Nonempty) (hA : A.Nonempty) :
    connectivity K S <= expansion K S A := (le_connectivity_iff hK hS).1 le_rfl hA

/--
lemma `connectivity_nonneg` / 引理 `connectivity_nonneg`

English:
lemma connectivity_nonneg
  given: (hK : K <= 1) (hS : S.Nonempty)
  proof: by simp [*]

中文:
引理 connectivity_nonneg
  条件: (hK : K <= 1) (hS : S.非空)
  证明: by simp [*]
-/
private lemma connectivity_nonneg (hK : K <= 1) (hS : S.Nonempty) :
    0 <= connectivity K S := by simp [*]

/--
Definition of `IsFragment` / `IsFragment` 的定义

English:
definition IsFragment
  signature: (K : Real) (S A : Finset G)
  body: expansion K S A = connectivity K S

中文:
定义 IsFragment
  签名: (K : 实数) (S A : 有限集 G)
  定义体: expansion K S A = connectivity K S
-/
private def IsFragment (K : Real) (S A : Finset G) : Prop := expansion K S A = connectivity K S

/--
Definition of `IsAtom` / `IsAtom` 的定义

English:
definition IsAtom
  signature: (K : Real) (S A : Finset G)
  body: MinimalFor (IsFragment K S) card A

中文:
定义 IsAtom
  签名: (K : 实数) (S A : 有限集 G)
  定义体: MinimalFor (IsFragment K S) card A
-/
private def IsAtom (K : Real) (S A : Finset G) : Prop := MinimalFor (IsFragment K S) card A

/--
lemma `IsAtom.isFragment` / 引理 `IsAtom.isFragment`

English:
lemma IsAtom.isFragment
  given: (hA : IsAtom K S A)
  statement: IsFragment K S A
  proof: hA.1

中文:
引理 IsAtom.isFragment
  条件: (hA : IsAtom K S A)
  结论: IsFragment K S A
  证明: hA.1
-/
private lemma IsAtom.isFragment (hA : IsAtom K S A) : IsFragment K S A := hA.1

/--
lemma `isFragment_smul_finset` / 引理 `isFragment_smul_finset`

English:
lemma isFragment_smul_finset
  statement: IsFragment K S (a • A) ↔ IsFragment K S A
  proof: by
  simp [IsFragment]

中文:
引理 isFragment_smul_finset
  结论: IsFragment K S (a • A) ↔ IsFragment K S A
  证明: by
  simp [IsFragment]
-/
@[simp] private lemma isFragment_smul_finset : IsFragment K S (a • A) ↔ IsFragment K S A := by
  simp [IsFragment]

/--
lemma `isAtom_smul_finset` / 引理 `isAtom_smul_finset`

English:
lemma isAtom_smul_finset
  statement: IsAtom K S (a • A) ↔ IsAtom K S A
  proof: by
  simp [IsAtom, MinimalFor]

中文:
引理 isAtom_smul_finset
  结论: IsAtom K S (a • A) ↔ IsAtom K S A
  证明: by
  simp [IsAtom, MinimalFor]
-/
@[simp] private lemma isAtom_smul_finset : IsAtom K S (a • A) ↔ IsAtom K S A := by
  simp [IsAtom, MinimalFor]

/--
lemma `IsFragment.smul_finset` / 引理 `IsFragment.smul_finset`

English:
lemma IsFragment.smul_finset
  given: (a : G) (hA : IsFragment K S A)
  statement: IsFragment K S (a • A)
  proof: isFragment_smul_finset.2 hA

中文:
引理 IsFragment.smul_finset
  条件: (a : G) (hA : IsFragment K S A)
  结论: IsFragment K S (a • A)
  证明: isFragment_smul_finset.2 hA
-/
private lemma IsFragment.smul_finset (a : G) (hA : IsFragment K S A) : IsFragment K S (a • A) :=
  isFragment_smul_finset.2 hA

/--
lemma `IsAtom.smul_finset` / 引理 `IsAtom.smul_finset`

English:
lemma IsAtom.smul_finset
  given: (a : G) (hA : IsAtom K S A)
  statement: IsAtom K S (a • A)
  proof: isAtom_smul_finset.2 hA

中文:
引理 IsAtom.smul_finset
  条件: (a : G) (hA : IsAtom K S A)
  结论: IsAtom K S (a • A)
  证明: isAtom_smul_finset.2 hA
-/
private lemma IsAtom.smul_finset (a : G) (hA : IsAtom K S A) : IsAtom K S (a • A) :=
  isAtom_smul_finset.2 hA

/--
lemma `IsFragment.inter` / 引理 `IsFragment.inter`

English:
lemma IsFragment.inter
  statement: (hK : K <= 1) (hS : S.Nonempty) (hA : IsFragment K S A)
  proof: by
  unfold IsFragment at *
  have := expansion_submodularity (S := S) (A := A) (B := B) (K := K)
  have := connectivity_le_expansion hK hS hAB
have := connectivity_le_expansion hK hS hAB.mono inter_subset_union
  linarith

中文:
引理 IsFragment.inter
  结论: (hK : K <= 1) (hS : S.非空) (hA : IsFragment K S A)
  证明: by
  unfold IsFragment at *
  have := expansion_submodularity (S := S) (A := A) (B := B) (K := K)
  have := connectivity_le_expansion hK hS hAB
have := connectivity_le_expansion hK hS hAB.mono inter_subset_union
  linarith
-/
private lemma IsFragment.inter (hK : K <= 1) (hS : S.Nonempty) (hA : IsFragment K S A)
    (hB : IsFragment K S B) (hAB : (A inter B).Nonempty) : IsFragment K S (A inter B) := by
  unfold IsFragment at *
  have := expansion_submodularity (S := S) (A := A) (B := B) (K := K)
  have := connectivity_le_expansion hK hS hAB
have := connectivity_le_expansion hK hS hAB.mono inter_subset_union
  linarith

/--
lemma `IsAtom.eq_of_inter_nonempty` / 引理 `IsAtom.eq_of_inter_nonempty`

English:
lemma IsAtom.eq_of_inter_nonempty
  statement: (hK : K <= 1) (hS : S.Nonempty)
  proof: by
  replace hAB := hA.isFragment.inter hK hS hB.isFragment hAB
replace hA := hA.2 hAB by grw [inter_subset_left]
replace hB := hB.2 hAB by grw [inter_subset_right]
  replace hA := eq_of_subset_of_card_le inter_subset_left hA
  replace hB := eq_of_subset_of_card_le inter_subset_right hB
  exact hA.symm.trans hB

中文:
引理 IsAtom.eq_of_inter_nonempty
  结论: (hK : K <= 1) (hS : S.非空)
  证明: by
  replace hAB := hA.isFragment.inter hK hS hB.isFragment hAB
replace hA := hA.2 hAB by grw [inter_subset_left]
replace hB := hB.2 hAB by grw [inter_subset_right]
  replace hA := eq_of_subset_of_card_le inter_subset_left hA
  replace hB := eq_of_subset_of_card_le inter_subset_right hB
  exact hA.symm.trans hB

Depends on / 依赖: Dir.left, L.exists_cons, List.Vector.toList, List.length_reverse, List.reverseAux, List.reverse_reverse, ListBlank, ListBlank.append, ListBlank.cons_flatMap, ListBlank.head_cons, ListBlank.tail_cons, Tape.mk, Tape.move, Vector, Vector.toList_length, append, cons_flatMap, exists_cons, head_cons, length
-/
private lemma IsAtom.eq_of_inter_nonempty (hK : K <= 1) (hS : S.Nonempty)
    (hA : IsAtom K S A) (hB : IsAtom K S B) (hAB : (A inter B).Nonempty) : A = B := by
  replace hAB := hA.isFragment.inter hK hS hB.isFragment hAB
replace hA := hA.2 hAB by grw [inter_subset_left]
replace hB := hB.2 hAB by grw [inter_subset_right]
  replace hA := eq_of_subset_of_card_le inter_subset_left hA
  replace hB := eq_of_subset_of_card_le inter_subset_right hB
  exact hA.symm.trans hB

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
lemma `exists_nonempty_isFragment` / 引理 `exists_nonempty_isFragment`

English:
lemma exists_nonempty_isFragment
  given: (hK : K < 1) (hS : S.Nonempty)
  proof: by
  -- We will show this lemma by contradiction. So we suppose that the infimum in the definition of
  -- connectivity is not attained by a nonempty finite subset of `G`, or, equivalently, that for
  -- every `κ < k` where `κ` is the connectivity, there is nonempty `A` such that `κ < ex A < k`.
  by_contra! H
  let ex := expansion K S
  let κ := connectivity K S
  -- Some useful calculations
  have κ_add_one_pos : 0 < κ + 1 := by linarith [connectivity_nonneg hK.le hS]
  have one_sub_K_pos : 0 < 1 - K := by linarith
  -- First we show that for large enough `A`, `κ + 1 < ex A`. Calculations show that
  -- `#A > ⌊(κ + 1) / (1 - K)⌋` suffices. We will actually use the contrapositive of this result: if
  -- `ex A` is near `κ`, then `A` will need to be small.
  let t := Nat.floor ((κ + 1) / (1 - K))
  have largeA {A : Finset G} (hA : t < #A) : κ + 1 < ex A := by
    rw [Nat.lt_iff_add_one_le] at hA
    calc
          κ + 1
      _ = (κ + 1) / ((κ + 1) / (1 - K)) * ((κ + 1) / (1 - K)) := by field
      _ < (κ + 1) / ((κ + 1) / (1 - K)) * (t + 1) := by gcongr; exact Nat.lt_floor_add_one _
      _ = (1 - K) * (t + 1) := by field
      _ <= (1 - K) * #A := by norm_cast; gcongr
      _ <= ex A := mul_card_le_expansion hS
  -- On the other hand, we essentially show that there are only finitely many possible values for
  -- `A` with `#A ≤ t`, and these values are found in the set `M = (⟦#S, t#S⟧ - K⟦1, t⟧) ∩ (κ, ∞)`.
  let M := {x in ((Icc #S (t * #S)).map Nat.castEmbedding -
    K • (Icc 1 t).map Nat.castEmbedding : Finset Real) | κ < x}
  have smallA {A : Finset G} (hA : A.Nonempty) (hAt : #A <= t) : ex A in M := by
    rw [mem_filter]
refine ⟨sub_mem_sub ?_ ?_, (connectivity_le_expansion hK.le hS hA).lt_of_ne' H _ hA⟩
    · apply mem_map_of_mem
      exact mem_Icc.2 ⟨card_le_card_mul_left hA, by grw [card_mul_le, hAt]⟩
    · apply smul_mem_smul_finset
      apply mem_map_of_mem
      exact mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.mpr hA.card_ne_zero, hAt⟩
  -- Now we take the minimum value of `M` (union `{κ + 1}` to handle the eventual emptiness of `M`
  -- and get better bounds). This will be strictly larger than `κ` by definition.
  have : (M union {κ + 1}).Nonempty := by simp
  let k := (M union {κ + 1}).min' this
  have : κ < k := by simp [k, M]
  -- By the property of infimum and the previous claim, there is `A` with `κ < ex A < k ≤ κ + 1`.
  -- But then the claim about large `A` implies that `#A ≤ t` and thus `ex A ∈ M` and `k ≤ ex A`,
  -- a contradiction.
  obtain ⟨A, hA, hAk⟩ := (connectivity_lt_iff hK.le hS).mp this
have : ex A <= κ + 1 := hAk.le.trans min'_le _ _ (by simp)
  have := not_lt.mp (mt largeA this.not_gt)
exact hAk.not_ge min'_le (M union {κ + 1}) _ subset_union_left smallA hA this

中文:
引理 存在_nonempty_isFragment
  条件: (hK : K < 1) (hS : S.非空)
  证明: by
  -- We will show this lemma by contradiction. So we suppose that the infimum in the definition of
  -- connectivity is not attained by a nonempty finite subset of `G`, or, equivalently, that for
  -- every `κ < k` where `κ` is the connectivity, there is nonempty `A` such that `κ < ex A < k`.
  by_contra! H
  let ex := expansion K S
  let κ := connectivity K S
  -- Some useful calculations
  have κ_add_one_pos : 0 < κ + 1 := by linarith [connectivity_nonneg hK.le hS]
  have one_sub_K_pos : 0 < 1 - K := by linarith
  -- First we show that for large enough `A`, `κ + 1 < ex A`. Calculations show that
  -- `#A > ⌊(κ + 1) / (1 - K)⌋` suffices. We will actually use the contrapositive of this result: if
  -- `ex A` is near `κ`, then `A` will need to be small.
  let t := Nat.floor ((κ + 1) / (1 - K))
  have largeA {A : Finset G} (hA : t < #A) : κ + 1 < ex A := by
    rw [Nat.lt_iff_add_one_le] at hA
    calc
          κ + 1
      _ = (κ + 1) / ((κ + 1) / (1 - K)) * ((κ + 1) / (1 - K)) := by field
      _ < (κ + 1) / ((κ + 1) / (1 - K)) * (t + 1) := by gcongr; exact Nat.lt_floor_add_one _
      _ = (1 - K) * (t + 1) := by field
      _ <= (1 - K) * #A := by norm_cast; gcongr
      _ <= ex A := mul_card_le_expansion hS
  -- On the other hand, we essentially show that there are only finitely many possible values for
  -- `A` with `#A ≤ t`, and these values are found in the set `M = (⟦#S, t#S⟧ - K⟦1, t⟧) ∩ (κ, ∞)`.
  let M := {x in ((Icc #S (t * #S)).map Nat.castEmbedding -
    K • (Icc 1 t).map Nat.castEmbedding : Finset Real) | κ < x}
  have smallA {A : Finset G} (hA : A.Nonempty) (hAt : #A <= t) : ex A in M := by
    rw [mem_filter]
refine ⟨sub_mem_sub ?_ ?_, (connectivity_le_expansion hK.le hS hA).lt_of_ne' H _ hA⟩
    · apply mem_map_of_mem
      exact mem_Icc.2 ⟨card_le_card_mul_left hA, by grw [card_mul_le, hAt]⟩
    · apply smul_mem_smul_finset
      apply mem_map_of_mem
      exact mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.mpr hA.card_ne_zero, hAt⟩
  -- Now we take the minimum value of `M` (union `{κ + 1}` to handle the eventual emptiness of `M`
  -- and get better bounds). This will be strictly larger than `κ` by definition.
  have : (M union {κ + 1}).Nonempty := by simp
  let k := (M union {κ + 1}).min' this
  have : κ < k := by simp [k, M]
  -- By the property of infimum and the previous claim, there is `A` with `κ < ex A < k ≤ κ + 1`.
  -- But then the claim about large `A` implies that `#A ≤ t` and thus `ex A ∈ M` and `k ≤ ex A`,
  -- a contradiction.
  obtain ⟨A, hA, hAk⟩ := (connectivity_lt_iff hK.le hS).mp this
have : ex A <= κ + 1 := hAk.le.trans min'_le _ _ (by simp)
  have := not_lt.mp (mt largeA this.not_gt)
exact hAk.not_ge min'_le (M union {κ + 1}) _ subset_union_left smallA hA this

Depends on / 依赖: Dir.left, Dir.right, Eq.symm, ListBlank, ListBlank.cons_head_tail, ListBlank.head_cons, ListBlank.tail_cons, Tape.move, Tape.move_left_right, _move_left, cons_head_tail, head_cons, iterate_succ_apply, move_left_right, tail_cons, trTape
-/
private lemma exists_nonempty_isFragment (hK : K < 1) (hS : S.Nonempty) :
    exists A, A.Nonempty ∧ IsFragment K S A := by
  -- We will show this lemma by contradiction. So we suppose that the infimum in the definition of
  -- connectivity is not attained by a nonempty finite subset of `G`, or, equivalently, that for
  -- every `κ < k` where `κ` is the connectivity, there is nonempty `A` such that `κ < ex A < k`.
  by_contra! H
  let ex := expansion K S
  let κ := connectivity K S
  -- Some useful calculations
  have κ_add_one_pos : 0 < κ + 1 := by linarith [connectivity_nonneg hK.le hS]
  have one_sub_K_pos : 0 < 1 - K := by linarith
  -- First we show that for large enough `A`, `κ + 1 < ex A`. Calculations show that
  -- `#A > ⌊(κ + 1) / (1 - K)⌋` suffices. We will actually use the contrapositive of this result: if
  -- `ex A` is near `κ`, then `A` will need to be small.
  let t := Nat.floor ((κ + 1) / (1 - K))
  have largeA {A : Finset G} (hA : t < #A) : κ + 1 < ex A := by
    rw [Nat.lt_iff_add_one_le] at hA
    calc
          κ + 1
      _ = (κ + 1) / ((κ + 1) / (1 - K)) * ((κ + 1) / (1 - K)) := by field
      _ < (κ + 1) / ((κ + 1) / (1 - K)) * (t + 1) := by gcongr; exact Nat.lt_floor_add_one _
      _ = (1 - K) * (t + 1) := by field
      _ <= (1 - K) * #A := by norm_cast; gcongr
      _ <= ex A := mul_card_le_expansion hS
  -- On the other hand, we essentially show that there are only finitely many possible values for
  -- `A` with `#A ≤ t`, and these values are found in the set `M = (⟦#S, t#S⟧ - K⟦1, t⟧) ∩ (κ, ∞)`.
  let M := {x in ((Icc #S (t * #S)).map Nat.castEmbedding -
    K • (Icc 1 t).map Nat.castEmbedding : Finset Real) | κ < x}
  have smallA {A : Finset G} (hA : A.Nonempty) (hAt : #A <= t) : ex A in M := by
    rw [mem_filter]
refine ⟨sub_mem_sub ?_ ?_, (connectivity_le_expansion hK.le hS hA).lt_of_ne' H _ hA⟩
    · apply mem_map_of_mem
      exact mem_Icc.2 ⟨card_le_card_mul_left hA, by grw [card_mul_le, hAt]⟩
    · apply smul_mem_smul_finset
      apply mem_map_of_mem
      exact mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.mpr hA.card_ne_zero, hAt⟩
  -- Now we take the minimum value of `M` (union `{κ + 1}` to handle the eventual emptiness of `M`
  -- and get better bounds). This will be strictly larger than `κ` by definition.
  have : (M union {κ + 1}).Nonempty := by simp
  let k := (M union {κ + 1}).min' this
  have : κ < k := by simp [k, M]
  -- By the property of infimum and the previous claim, there is `A` with `κ < ex A < k ≤ κ + 1`.
  -- But then the claim about large `A` implies that `#A ≤ t` and thus `ex A ∈ M` and `k ≤ ex A`,
  -- a contradiction.
  obtain ⟨A, hA, hAk⟩ := (connectivity_lt_iff hK.le hS).mp this
have : ex A <= κ + 1 := hAk.le.trans min'_le _ _ (by simp)
  have := not_lt.mp (mt largeA this.not_gt)
exact hAk.not_ge min'_le (M union {κ + 1}) _ subset_union_left smallA hA this

/--
lemma `exists_isFragment` / 引理 `exists_isFragment`

English:
lemma exists_isFragment
  given: (hK : K < 1) (hS : S.Nonempty)
  proof: let ⟨A, _, hA⟩ := exists_nonempty_isFragment hK hS; ⟨A, hA⟩

中文:
引理 存在_isFragment
  条件: (hK : K < 1) (hS : S.非空)
  证明: let ⟨A, _, hA⟩ := exists_nonempty_isFragment hK hS; ⟨A, hA⟩
-/
private lemma exists_isFragment (hK : K < 1) (hS : S.Nonempty) :
    exists A, IsFragment K S A := let ⟨A, _, hA⟩ := exists_nonempty_isFragment hK hS; ⟨A, hA⟩

/--
lemma `exists_isAtom` / 引理 `exists_isAtom`

English:
lemma exists_isAtom
  given: (hK : K < 1) (hS : S.Nonempty)
  statement: exists A, IsAtom K S A
  proof: exists_minimalFor_of_wellFoundedLT _ _ exists_isFragment hK hS

中文:
引理 存在_isAtom
  条件: (hK : K < 1) (hS : S.非空)
  结论: 存在 A, IsAtom K S A
  证明: exists_minimalFor_of_wellFoundedLT _ _ exists_isFragment hK hS
-/
private lemma exists_isAtom (hK : K < 1) (hS : S.Nonempty) : exists A, IsAtom K S A :=
exists_minimalFor_of_wellFoundedLT _ _ exists_isFragment hK hS

/--
lemma `connectivity_pos` / 引理 `connectivity_pos`

English:
lemma connectivity_pos
  given: (hK : K < 1) (hS : S.Nonempty)
  statement: 0 < connectivity K S
  proof: by
  obtain ⟨A, hA, hSA⟩ := exists_nonempty_isFragment hK hS
  exact (expansion_pos hK hS hA).trans_eq hSA

中文:
引理 connectivity_pos
  条件: (hK : K < 1) (hS : S.非空)
  结论: 0 < connectivity K S
  证明: by
  obtain ⟨A, hA, hSA⟩ := exists_nonempty_isFragment hK hS
  exact (expansion_pos hK hS hA).trans_eq hSA
-/
private lemma connectivity_pos (hK : K < 1) (hS : S.Nonempty) : 0 < connectivity K S := by
  obtain ⟨A, hA, hSA⟩ := exists_nonempty_isFragment hK hS
  exact (expansion_pos hK hS hA).trans_eq hSA

/--
lemma `not_isFragment_empty` / 引理 `not_isFragment_empty`

English:
lemma not_isFragment_empty
  given: (hK : K < 1) (hS : S.Nonempty)
  statement: ¬ IsFragment K S ∅
  proof: by
  simp [IsFragment, (connectivity_pos hK hS).ne]

中文:
引理 not_isFragment_empty
  条件: (hK : K < 1) (hS : S.非空)
  结论: ¬ IsFragment K S ∅
  证明: by
  simp [IsFragment, (connectivity_pos hK hS).ne]
-/
private lemma not_isFragment_empty (hK : K < 1) (hS : S.Nonempty) : ¬ IsFragment K S ∅ := by
  simp [IsFragment, (connectivity_pos hK hS).ne]

/--
lemma `IsFragment.nonempty` / 引理 `IsFragment.nonempty`

English:
lemma IsFragment.nonempty
  given: (hK : K < 1) (hS : S.Nonempty) (hA : IsFragment K S A)
  proof: by
  by_contra! rfl
  simp [*, not_isFragment_empty hK hS] at hA

中文:
引理 IsFragment.nonempty
  条件: (hK : K < 1) (hS : S.非空) (hA : IsFragment K S A)
  证明: by
  by_contra! rfl
  simp [*, not_isFragment_empty hK hS] at hA
-/
private lemma IsFragment.nonempty (hK : K < 1) (hS : S.Nonempty) (hA : IsFragment K S A) :
    A.Nonempty := by
  by_contra! rfl
  simp [*, not_isFragment_empty hK hS] at hA

/--
lemma `IsAtom.nonempty` / 引理 `IsAtom.nonempty`

English:
lemma IsAtom.nonempty
  given: (hK : K < 1) (hS : S.Nonempty) (hA : IsAtom K S A)
  statement: A.Nonempty
  proof: hA.isFragment.nonempty hK hS

中文:
引理 IsAtom.nonempty
  条件: (hK : K < 1) (hS : S.非空) (hA : IsAtom K S A)
  结论: A.非空
  证明: hA.isFragment.nonempty hK hS
-/
private lemma IsAtom.nonempty (hK : K < 1) (hS : S.Nonempty) (hA : IsAtom K S A) : A.Nonempty :=
  hA.isFragment.nonempty hK hS

/--
lemma `exists_subgroup_isAtom` / 引理 `exists_subgroup_isAtom`

English:
lemma exists_subgroup_isAtom
  given: (hK : K < 1) (hS : S.Nonempty)
  proof: by
  -- We take any atom `N` of `G` with respect to `K` and `S`. Since left multiples of `N` (which
  -- are atoms as well) partition `G` by `IsAtom.eq_of_inter_nonempty`, we will deduce that a left
  -- multiple that contains `1` is a (finite) subgroup of `G`.
  obtain ⟨N, hN⟩ := exists_isAtom hK hS
  obtain ⟨n, hn⟩ := IsAtom.nonempty hK hS hN
  have one_mem_carrier : 1 in n⁻¹ •> N := by simpa [mem_inv_smul_finset_iff]
  have self_mem_smul_carrier (x : G) : x in x • n⁻¹ • N := by
    apply smul_mem_smul_finset (a := x) at one_mem_carrier
    simpa only [smul_eq_mul, mul_one] using! one_mem_carrier
  let H : Subgroup G := {
    carrier := n⁻¹ •> N
    one_mem' := mod_cast one_mem_carrier
    mul_mem' {a b} ha hb := by
      rw [← coe_smul_finset]; rw [mem_coe] at *
      apply smul_mem_smul_finset (a := a) at hb
      rw [smul_eq_mul] at hb
      have : (n⁻¹ •> N inter a •> n⁻¹ •> N).Nonempty := ⟨a, by
        simpa only [mem_inter] using! ⟨ha, self_mem_smul_carrier a⟩⟩
      simpa only [← (hN.smul_finset n⁻¹).eq_of_inter_nonempty hK.le hS
        ((hN.smul_finset n⁻¹).smul_finset a) this] using! hb
    inv_mem' {a} ha := by
      rw [← coe_smul_finset]; rw [mem_coe] at *
      apply smul_mem_smul_finset (a := a⁻¹) at ha
      rw [smul_eq_mul]; rw [inv_mul_cancel] at ha
      have : (n⁻¹ •> N inter a⁻¹ •> n⁻¹ •> N).Nonempty := ⟨1, by simpa using! ⟨one_mem_carrier, ha⟩⟩
      simpa only [← (hN.smul_finset n⁻¹).eq_of_inter_nonempty hK.le hS
        ((hN.smul_finset n⁻¹).smul_finset a⁻¹) this] using! self_mem_smul_carrier a⁻¹
  }
  refine ⟨H, Fintype.ofFinset (n⁻¹ •> N) fun a => ?_, ?_⟩
  · simpa only [← mem_coe, coe_smul_finset] using! H.mem_carrier
  · simpa [Set.toFinset_smul_set, toFinset_coe, H] using! IsAtom.smul_finset n⁻¹ hN

中文:
引理 存在_subgroup_isAtom
  条件: (hK : K < 1) (hS : S.非空)
  证明: by
  -- We take any atom `N` of `G` with respect to `K` and `S`. Since left multiples of `N` (which
  -- are atoms as well) partition `G` by `IsAtom.eq_of_inter_nonempty`, we will deduce that a left
  -- multiple that contains `1` is a (finite) subgroup of `G`.
  obtain ⟨N, hN⟩ := exists_isAtom hK hS
  obtain ⟨n, hn⟩ := IsAtom.nonempty hK hS hN
  have one_mem_carrier : 1 in n⁻¹ •> N := by simpa [mem_inv_smul_finset_iff]
  have self_mem_smul_carrier (x : G) : x in x • n⁻¹ • N := by
    apply smul_mem_smul_finset (a := x) at one_mem_carrier
    simpa only [smul_eq_mul, mul_one] using! one_mem_carrier
  let H : Subgroup G := {
    carrier := n⁻¹ •> N
    one_mem' := mod_cast one_mem_carrier
    mul_mem' {a b} ha hb := by
      rw [← coe_smul_finset]; rw [mem_coe] at *
      apply smul_mem_smul_finset (a := a) at hb
      rw [smul_eq_mul] at hb
      have : (n⁻¹ •> N inter a •> n⁻¹ •> N).Nonempty := ⟨a, by
        simpa only [mem_inter] using! ⟨ha, self_mem_smul_carrier a⟩⟩
      simpa only [← (hN.smul_finset n⁻¹).eq_of_inter_nonempty hK.le hS
        ((hN.smul_finset n⁻¹).smul_finset a) this] using! hb
    inv_mem' {a} ha := by
      rw [← coe_smul_finset]; rw [mem_coe] at *
      apply smul_mem_smul_finset (a := a⁻¹) at ha
      rw [smul_eq_mul]; rw [inv_mul_cancel] at ha
      have : (n⁻¹ •> N inter a⁻¹ •> n⁻¹ •> N).Nonempty := ⟨1, by simpa using! ⟨one_mem_carrier, ha⟩⟩
      simpa only [← (hN.smul_finset n⁻¹).eq_of_inter_nonempty hK.le hS
        ((hN.smul_finset n⁻¹).smul_finset a⁻¹) this] using! self_mem_smul_carrier a⁻¹
  }
  refine ⟨H, Fintype.ofFinset (n⁻¹ •> N) fun a => ?_, ?_⟩
  · simpa only [← mem_coe, coe_smul_finset] using! H.mem_carrier
  · simpa [Set.toFinset_smul_set, toFinset_coe, H] using! IsAtom.smul_finset n⁻¹ hN
-/
private lemma exists_subgroup_isAtom (hK : K < 1) (hS : S.Nonempty) :
    exists (H : Subgroup G) (_ : Fintype H), IsAtom K S (Set.toFinset H) := by
  -- We take any atom `N` of `G` with respect to `K` and `S`. Since left multiples of `N` (which
  -- are atoms as well) partition `G` by `IsAtom.eq_of_inter_nonempty`, we will deduce that a left
  -- multiple that contains `1` is a (finite) subgroup of `G`.
  obtain ⟨N, hN⟩ := exists_isAtom hK hS
  obtain ⟨n, hn⟩ := IsAtom.nonempty hK hS hN
  have one_mem_carrier : 1 in n⁻¹ •> N := by simpa [mem_inv_smul_finset_iff]
  have self_mem_smul_carrier (x : G) : x in x • n⁻¹ • N := by
    apply smul_mem_smul_finset (a := x) at one_mem_carrier
    simpa only [smul_eq_mul, mul_one] using! one_mem_carrier
  let H : Subgroup G := {
    carrier := n⁻¹ •> N
    one_mem' := mod_cast one_mem_carrier
    mul_mem' {a b} ha hb := by
      rw [← coe_smul_finset]; rw [mem_coe] at *
      apply smul_mem_smul_finset (a := a) at hb
      rw [smul_eq_mul] at hb
      have : (n⁻¹ •> N inter a •> n⁻¹ •> N).Nonempty := ⟨a, by
        simpa only [mem_inter] using! ⟨ha, self_mem_smul_carrier a⟩⟩
      simpa only [← (hN.smul_finset n⁻¹).eq_of_inter_nonempty hK.le hS
        ((hN.smul_finset n⁻¹).smul_finset a) this] using! hb
    inv_mem' {a} ha := by
      rw [← coe_smul_finset]; rw [mem_coe] at *
      apply smul_mem_smul_finset (a := a⁻¹) at ha
      rw [smul_eq_mul]; rw [inv_mul_cancel] at ha
      have : (n⁻¹ •> N inter a⁻¹ •> n⁻¹ •> N).Nonempty := ⟨1, by simpa using! ⟨one_mem_carrier, ha⟩⟩
      simpa only [← (hN.smul_finset n⁻¹).eq_of_inter_nonempty hK.le hS
        ((hN.smul_finset n⁻¹).smul_finset a⁻¹) this] using! self_mem_smul_carrier a⁻¹
  }
  refine ⟨H, Fintype.ofFinset (n⁻¹ •> N) fun a => ?_, ?_⟩
  · simpa only [← mem_coe, coe_smul_finset] using! H.mem_carrier
  · simpa [Set.toFinset_smul_set, toFinset_coe, H] using! IsAtom.smul_finset n⁻¹ hN

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
theorem `card_mul_finset_lt_two` / 定理 `card_mul_finset_lt_two`

English:
theorem card_mul_finset_lt_two
  statement: {ε : Real} (hε₀ : 0 < ε) (hε₁ : ε <= 1) (hS : S.Nonempty)
  proof: by
  let K := 1 - ε / 2
  have hK : K < 1 := by unfold K; linarith [hε₀]
  let ex := expansion K S
  let κ := connectivity K S
  -- We will show that an atomic subgroup `H ≤ G` with respect to `K` and `S` and the right coset
  -- representing finset of `S` acting on `H` are adequate choices for the theorem
  obtain ⟨H, _, hH⟩ := exists_subgroup_isAtom hK hS
  obtain ⟨Z, hZS, hHZS, hZinj⟩ := exists_subset_mul_eq_mul_injOn H S
  -- We only use the existence of `A` given by assumption to get a good bound on `ex H` solely
  -- in terms of `#S` and `ε`.
  obtain ⟨A, hA₁, hA₂⟩ := hA
  have calc₁ : ex (Set.toFinset H) <= (1 - ε / 2) * #S := by
    calc
          ex (Set.toFinset H)
      _ = κ := hH.isFragment
      _ <= #(A * S) - K * #A :=
connectivity_le_expansion hK.le hS card_pos.mp hS.card_pos.trans_le hA₁
      _ <= (2 - ε) * #S - (1 - ε / 2) * #S := by gcongr; linarith
      _ = (1 - ε / 2) * #S := by linarith
  refine ⟨H, inferInstance, Z, ?cardH, ?cardZ, by
    simpa only [hHZS] using Set.subset_mul_right _ H.one_mem⟩
  -- Bound on `#H` follows easily from the previous calculation.
  case cardH =>
    rw [← mul_le_mul_iff_right₀ (a := ε / 2) (by positivity)]
    calc
            ε / 2 * (Fintype.card H)
        _ = ε / 2 * #(H : Set G).toFinset := by
          simp only [Set.toFinset_card, SetLike.coe_sort_coe]
        _ = (1 - K) * #(H : Set G).toFinset := by ring
        _ <= ex (Set.toFinset H) := mul_card_le_expansion hS
        _ <= (1 - ε / 2) * #S := calc₁
        _ = ε / 2 * ((2 / ε - 1) * #S) := by field
  -- To show the bound on `#Z`, we note that `#Z = #(HS) / #H` and show `#(HS) ≤ (2 / ε - 1) * #H`.
  case cardZ =>
    calc
          (#Z : Real)
      _ = #(H : Set G).toFinset * #Z / #(H : Set G).toFinset := by field
      _ = #(Set.toFinset H * Z) / #(H : Set G).toFinset := by
        simp [← card_mul_eq_mul_card_of_injOn_opSMul hZinj, Nat.cast_mul]
      _ = #(Set.toFinset H * S) / #(H : Set G).toFinset := by
        congr 3; simpa using congr(($hHZS).toFinset)
      _ <= (2 / ε - 1) * #(H : Set G).toFinset / #(H : Set G).toFinset := ?_
      _ = 2 / ε - 1 := by field
    gcongr
    -- Finally, to show `#(HS) ≤ (2 / ε - 1) * #H`, we multiply both sides by `1 - K = ε / 2` and
    -- show `#(HS) = K * #H + ex H ≤ K * #H + (1 - ε / 2) * #S ≤ K * #H + (1 - ε / 2) * #(HS)`,
    -- where we used `calc₁` again.
    rw [← mul_le_mul_iff_right₀ (show 0 < 1 - K by linarith [hK])]
    suffices (1 - K) * #(Set.toFinset H * S) <= (1 - ε / 2) * #(H : Set G).toFinset by
      apply le_of_le_of_eq this; simp [K]; field
    rw [sub_mul]; rw [one_mul]; rw [sub_le_iff_le_add]
    calc
          (#(Set.toFinset H * S) : Real)
      _ = K * #(H : Set G).toFinset + (#(Set.toFinset H * S) - K * #(H : Set G).toFinset) := by ring
      _ = K * #(H : Set G).toFinset + ex (Set.toFinset H) := rfl
      _ <= K * #(H : Set G).toFinset + (1 - ε / 2) * #(Set.toFinset H * S) := by
        grw [calc₁]
        gcongr
        · linarith
        · simp only [Set.mem_toFinset, SetLike.mem_coe, H.one_mem, subset_mul_right]

中文:
定理 card_mul_finset_lt_two
  结论: {ε : 实数} (hε₀ : 0 < ε) (hε₁ : ε <= 1) (hS : S.非空)
  证明: by
  let K := 1 - ε / 2
  have hK : K < 1 := by unfold K; linarith [hε₀]
  let ex := expansion K S
  let κ := connectivity K S
  -- We will show that an atomic subgroup `H ≤ G` with respect to `K` and `S` and the right coset
  -- representing finset of `S` acting on `H` are adequate choices for the theorem
  obtain ⟨H, _, hH⟩ := exists_subgroup_isAtom hK hS
  obtain ⟨Z, hZS, hHZS, hZinj⟩ := exists_subset_mul_eq_mul_injOn H S
  -- We only use the existence of `A` given by assumption to get a good bound on `ex H` solely
  -- in terms of `#S` and `ε`.
  obtain ⟨A, hA₁, hA₂⟩ := hA
  have calc₁ : ex (Set.toFinset H) <= (1 - ε / 2) * #S := by
    calc
          ex (Set.toFinset H)
      _ = κ := hH.isFragment
      _ <= #(A * S) - K * #A :=
connectivity_le_expansion hK.le hS card_pos.mp hS.card_pos.trans_le hA₁
      _ <= (2 - ε) * #S - (1 - ε / 2) * #S := by gcongr; linarith
      _ = (1 - ε / 2) * #S := by linarith
  refine ⟨H, inferInstance, Z, ?cardH, ?cardZ, by
    simpa only [hHZS] using Set.subset_mul_right _ H.one_mem⟩
  -- Bound on `#H` follows easily from the previous calculation.
  case cardH =>
    rw [← mul_le_mul_iff_right₀ (a := ε / 2) (by positivity)]
    calc
            ε / 2 * (Fintype.card H)
        _ = ε / 2 * #(H : Set G).toFinset := by
          simp only [Set.toFinset_card, SetLike.coe_sort_coe]
        _ = (1 - K) * #(H : Set G).toFinset := by ring
        _ <= ex (Set.toFinset H) := mul_card_le_expansion hS
        _ <= (1 - ε / 2) * #S := calc₁
        _ = ε / 2 * ((2 / ε - 1) * #S) := by field
  -- To show the bound on `#Z`, we note that `#Z = #(HS) / #H` and show `#(HS) ≤ (2 / ε - 1) * #H`.
  case cardZ =>
    calc
          (#Z : Real)
      _ = #(H : Set G).toFinset * #Z / #(H : Set G).toFinset := by field
      _ = #(Set.toFinset H * Z) / #(H : Set G).toFinset := by
        simp [← card_mul_eq_mul_card_of_injOn_opSMul hZinj, Nat.cast_mul]
      _ = #(Set.toFinset H * S) / #(H : Set G).toFinset := by
        congr 3; simpa using congr(($hHZS).toFinset)
      _ <= (2 / ε - 1) * #(H : Set G).toFinset / #(H : Set G).toFinset := ?_
      _ = 2 / ε - 1 := by field
    gcongr
    -- Finally, to show `#(HS) ≤ (2 / ε - 1) * #H`, we multiply both sides by `1 - K = ε / 2` and
    -- show `#(HS) = K * #H + ex H ≤ K * #H + (1 - ε / 2) * #S ≤ K * #H + (1 - ε / 2) * #(HS)`,
    -- where we used `calc₁` again.
    rw [← mul_le_mul_iff_right₀ (show 0 < 1 - K by linarith [hK])]
    suffices (1 - K) * #(Set.toFinset H * S) <= (1 - ε / 2) * #(H : Set G).toFinset by
      apply le_of_le_of_eq this; simp [K]; field
    rw [sub_mul]; rw [one_mul]; rw [sub_le_iff_le_add]
    calc
          (#(Set.toFinset H * S) : Real)
      _ = K * #(H : Set G).toFinset + (#(Set.toFinset H * S) - K * #(H : Set G).toFinset) := by ring
      _ = K * #(H : Set G).toFinset + ex (Set.toFinset H) := rfl
      _ <= K * #(H : Set G).toFinset + (1 - ε / 2) * #(Set.toFinset H * S) := by
        grw [calc₁]
        gcongr
        · linarith
        · simp only [Set.mem_toFinset, SetLike.mem_coe, H.one_mem, subset_mul_right]

Depends on / 依赖: connectivity, expansion
-/
theorem card_mul_finset_lt_two {ε : Real} (hε₀ : 0 < ε) (hε₁ : ε <= 1) (hS : S.Nonempty)
    (hA : exists A : Finset G, #S <= #A ∧ #(A * S) <= (2 - ε) * #S) :
    exists (H : Subgroup G) (_ : Fintype H) (Z : Finset G),
      Fintype.card H <= (2 / ε - 1) * #S ∧ #Z <= 2 / ε - 1 ∧ (S : Set G) subseteq H * Z := by
  let K := 1 - ε / 2
  have hK : K < 1 := by unfold K; linarith [hε₀]
  let ex := expansion K S
  let κ := connectivity K S
  -- We will show that an atomic subgroup `H ≤ G` with respect to `K` and `S` and the right coset
  -- representing finset of `S` acting on `H` are adequate choices for the theorem
  obtain ⟨H, _, hH⟩ := exists_subgroup_isAtom hK hS
  obtain ⟨Z, hZS, hHZS, hZinj⟩ := exists_subset_mul_eq_mul_injOn H S
  -- We only use the existence of `A` given by assumption to get a good bound on `ex H` solely
  -- in terms of `#S` and `ε`.
  obtain ⟨A, hA₁, hA₂⟩ := hA
  have calc₁ : ex (Set.toFinset H) <= (1 - ε / 2) * #S := by
    calc
          ex (Set.toFinset H)
      _ = κ := hH.isFragment
      _ <= #(A * S) - K * #A :=
connectivity_le_expansion hK.le hS card_pos.mp hS.card_pos.trans_le hA₁
      _ <= (2 - ε) * #S - (1 - ε / 2) * #S := by gcongr; linarith
      _ = (1 - ε / 2) * #S := by linarith
  refine ⟨H, inferInstance, Z, ?cardH, ?cardZ, by
    simpa only [hHZS] using Set.subset_mul_right _ H.one_mem⟩
  -- Bound on `#H` follows easily from the previous calculation.
  case cardH =>
    rw [← mul_le_mul_iff_right₀ (a := ε / 2) (by positivity)]
    calc
            ε / 2 * (Fintype.card H)
        _ = ε / 2 * #(H : Set G).toFinset := by
          simp only [Set.toFinset_card, SetLike.coe_sort_coe]
        _ = (1 - K) * #(H : Set G).toFinset := by ring
        _ <= ex (Set.toFinset H) := mul_card_le_expansion hS
        _ <= (1 - ε / 2) * #S := calc₁
        _ = ε / 2 * ((2 / ε - 1) * #S) := by field
  -- To show the bound on `#Z`, we note that `#Z = #(HS) / #H` and show `#(HS) ≤ (2 / ε - 1) * #H`.
  case cardZ =>
    calc
          (#Z : Real)
      _ = #(H : Set G).toFinset * #Z / #(H : Set G).toFinset := by field
      _ = #(Set.toFinset H * Z) / #(H : Set G).toFinset := by
        simp [← card_mul_eq_mul_card_of_injOn_opSMul hZinj, Nat.cast_mul]
      _ = #(Set.toFinset H * S) / #(H : Set G).toFinset := by
        congr 3; simpa using congr(($hHZS).toFinset)
      _ <= (2 / ε - 1) * #(H : Set G).toFinset / #(H : Set G).toFinset := ?_
      _ = 2 / ε - 1 := by field
    gcongr
    -- Finally, to show `#(HS) ≤ (2 / ε - 1) * #H`, we multiply both sides by `1 - K = ε / 2` and
    -- show `#(HS) = K * #H + ex H ≤ K * #H + (1 - ε / 2) * #S ≤ K * #H + (1 - ε / 2) * #(HS)`,
    -- where we used `calc₁` again.
    rw [← mul_le_mul_iff_right₀ (show 0 < 1 - K by linarith [hK])]
    suffices (1 - K) * #(Set.toFinset H * S) <= (1 - ε / 2) * #(H : Set G).toFinset by
      apply le_of_le_of_eq this; simp [K]; field
    rw [sub_mul]; rw [one_mul]; rw [sub_le_iff_le_add]
    calc
          (#(Set.toFinset H * S) : Real)
      _ = K * #(H : Set G).toFinset + (#(Set.toFinset H * S) - K * #(H : Set G).toFinset) := by ring
      _ = K * #(H : Set G).toFinset + ex (Set.toFinset H) := rfl
      _ <= K * #(H : Set G).toFinset + (1 - ε / 2) * #(Set.toFinset H * S) := by
        grw [calc₁]
        gcongr
        · linarith
        · simp only [Set.mem_toFinset, SetLike.mem_coe, H.one_mem, subset_mul_right]

/--
theorem `doubling_lt_two` / 定理 `doubling_lt_two`

English:
theorem doubling_lt_two
  statement: {ε : Real} (hε₀ : 0 < ε) (hε₁ : ε <= 1) (hA₀ : A.Nonempty)
  proof: card_mul_finset_lt_two hε₀ hε₁ hA₀ ⟨A, by rfl, hA₁⟩

中文:
定理 doubling_lt_two
  结论: {ε : 实数} (hε₀ : 0 < ε) (hε₁ : ε <= 1) (hA₀ : A.非空)
  证明: card_mul_finset_lt_two hε₀ hε₁ hA₀ ⟨A, by rfl, hA₁⟩

Depends on / 依赖: card_mul_finset_lt_two
-/
theorem doubling_lt_two {ε : Real} (hε₀ : 0 < ε) (hε₁ : ε <= 1) (hA₀ : A.Nonempty)
    (hA₁ : #(A * A) <= (2 - ε) * #A) : exists (H : Subgroup G) (_ : Fintype H) (Z : Finset G),
      Fintype.card H <= (2 / ε - 1) * #A ∧ #Z <= 2 / ε - 1 ∧ (A : Set G) subseteq H * Z :=
  card_mul_finset_lt_two hε₀ hε₁ hA₀ ⟨A, by rfl, hA₁⟩

end Finset
