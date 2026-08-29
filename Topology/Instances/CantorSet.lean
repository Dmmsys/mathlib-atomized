/-
Copyright (c) 2024 Jana Göken. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artur Szafarczyk, Suraj Krishna M S, Jean-Baptiste Stiegler, Isabelle Dubois,
Tomáš Jakl, Lorenzo Zanichelli, Alina Yan, Emilie Uthaiwat, Jana Göken,
Filippo A. E. Nuccio
-/
module

public import Mathlib.Analysis.Real.OfDigits
public import Mathlib.Data.Stream.Init
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Field

/-!
# Ternary Cantor Set

This file defines the Cantor ternary set and proves a few properties.

## Main Definitions

* `preCantorSet n`: The order `n` pre-Cantor set, defined inductively as the union of the images
  under the functions `(· / 3)` and `((2 + ·) / 3)`, with `preCantorSet 0 := Set.Icc 0 1`, i.e.
  `preCantorSet 0` is the unit interval [0,1].
* `cantorSet`: The ternary Cantor set, defined as the intersection of all pre-Cantor sets.
* `cantorToTernary`: given a number `x` in the Cantor set, returns its ternary representation
  `(d₀, d₁, ...)` consisting only of digits `0` and `2`, such that `x = 0.d₀d₁...`
  (see `ofDigits_cantorToTernary`).
* `ofDigits_zero_two_sequence_mem_cantorSet`: any such sequence corresponds to a number
  in the Cantor set.
* `ofDigits_zero_two_sequence_unique`: such a representation is unique.
-/

@[expose] public section

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `preCantorSet` / `preCantorSet` 的定义

English:
definition preCantorSet
  signature: : Nat -> Set Real

中文:
定义 preCantorSet
  签名: : 自然数 -> Set 实数
-/
noncomputable def preCantorSet : Nat -> Set Real
  | 0 => Set.Icc 0 1
  | n + 1 => (· / 3) '' preCantorSet n union (fun x => (2 + x) / 3) '' preCantorSet n

/--
lemma `preCantorSet_zero` / 引理 `preCantorSet_zero`

English:
lemma preCantorSet_zero
  statement: preCantorSet 0 = Set.Icc 0 1
  proof: rfl

中文:
引理 preCantorSet_zero
  结论: preCantorSet 0 = Set.Icc 0 1
  证明: rfl
-/
@[simp] lemma preCantorSet_zero : preCantorSet 0 = Set.Icc 0 1 := rfl
/--
lemma `preCantorSet_succ` / 引理 `preCantorSet_succ`

English:
lemma preCantorSet_succ
  given: (n : Nat)
  proof: rfl

中文:
引理 preCantorSet_succ
  条件: (n : 自然数)
  证明: rfl
-/
@[simp] lemma preCantorSet_succ (n : Nat) :
    preCantorSet (n + 1) = (· / 3) '' preCantorSet n union (fun x => (2 + x) / 3) '' preCantorSet n :=
  rfl

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `cantorSet` / `cantorSet` 的定义

English:
definition cantorSet
  signature: : Set Real
  body: ⋂ n, preCantorSet n

中文:
定义 cantorSet
  签名: : Set 实数
  定义体: ⋂ n, preCantorSet n

Depends on / 依赖: preCantorSet
-/
noncomputable def cantorSet : Set Real := ⋂ n, preCantorSet n



/--
lemma `quarters_mem_preCantorSet` / 引理 `quarters_mem_preCantorSet`

English:
lemma quarters_mem_preCantorSet
  given: (n : Nat)
  statement: 1 / 4 in preCantorSet n ∧ 3 / 4 in preCantorSet n
  proof: by
  induction n with
  | zero =>
    simp only [preCantorSet_zero]
    refine ⟨⟨ ?_, ?_⟩, ?_, ?_⟩ <;> norm_num
  | succ n ih =>
    apply And.intro
    · -- goal: 1 / 4 ∈ preCantorSet (n + 1)
      -- follows by the inductive hypothesis, since 3 / 4 ∈ preCantorSet n
      exact Or.inl ⟨3 / 4, ih.2,

中文:
引理 quarters_mem_preCantorSet
  条件: (n : 自然数)
  结论: 1 / 4 in preCantorSet n ∧ 3 / 4 in preCantorSet n
  证明: by
  induction n with
  | zero =>
    simp only [preCantorSet_zero]
    refine ⟨⟨ ?_, ?_⟩, ?_, ?_⟩ <;> norm_num
  | succ n ih =>
    apply And.intro
    · -- goal: 1 / 4 ∈ preCantorSet (n + 1)
      -- follows by the inductive hypothesis, since 3 / 4 ∈ preCantorSet n
      exact Or.inl ⟨3 / 4, ih.2,

Depends on / 依赖: And.intro, preCantorSet, preCantorSet_zero
-/
lemma quarters_mem_preCantorSet (n : Nat) : 1 / 4 in preCantorSet n ∧ 3 / 4 in preCantorSet n := by
  induction n with
  | zero =>
    simp only [preCantorSet_zero]
    refine ⟨⟨ ?_, ?_⟩, ?_, ?_⟩ <;> norm_num
  | succ n ih =>
    apply And.intro
    · -- goal: 1 / 4 ∈ preCantorSet (n + 1)
      -- follows by the inductive hypothesis, since 3 / 4 ∈ preCantorSet n
      exact Or.inl ⟨3 / 4, ih.2, by norm_num⟩
    · -- goal: 3 / 4 ∈ preCantorSet (n + 1)
      -- follows by the inductive hypothesis, since 1 / 4 ∈ preCantorSet n
      exact Or.inr ⟨1 / 4, ih.1, by norm_num⟩

/--
lemma `quarter_mem_preCantorSet` / 引理 `quarter_mem_preCantorSet`

English:
lemma quarter_mem_preCantorSet
  given: (n : Nat)
  statement: 1 / 4 in preCantorSet n
  proof: (quarters_mem_preCantorSet n).1

中文:
引理 quarter_mem_preCantorSet
  条件: (n : 自然数)
  结论: 1 / 4 in preCantorSet n
  证明: (quarters_mem_preCantorSet n).1

Depends on / 依赖: quarters_mem_preCantorSet
-/
lemma quarter_mem_preCantorSet (n : Nat) : 1 / 4 in preCantorSet n := (quarters_mem_preCantorSet n).1

/--
theorem `quarter_mem_cantorSet` / 定理 `quarter_mem_cantorSet`

English:
theorem quarter_mem_cantorSet
  statement: 1 / 4 in cantorSet
  proof: Set.mem_iInter.mpr quarter_mem_preCantorSet

中文:
定理 quarter_mem_cantorSet
  结论: 1 / 4 in cantorSet
  证明: Set.mem_iInter.mpr quarter_mem_preCantorSet

Depends on / 依赖: Set.mem_iInter.mpr, mem_iInter, quarter_mem_preCantorSet
-/
theorem quarter_mem_cantorSet : 1 / 4 in cantorSet :=
  Set.mem_iInter.mpr quarter_mem_preCantorSet

/--
lemma `zero_mem_preCantorSet` / 引理 `zero_mem_preCantorSet`

English:
lemma zero_mem_preCantorSet
  given: (n : Nat)
  statement: 0 in preCantorSet n
  proof: by
  induction n with
  | zero =>
    simp [preCantorSet]
  | succ n ih =>
    exact Or.inl ⟨0, ih, by simp only [zero_div]⟩

中文:
引理 zero_mem_preCantorSet
  条件: (n : 自然数)
  结论: 0 in preCantorSet n
  证明: by
  induction n with
  | zero =>
    simp [preCantorSet]
  | succ n ih =>
    exact Or.inl ⟨0, ih, by simp only [zero_div]⟩

Depends on / 依赖: Or.inl, preCantorSet, zero_div
-/
lemma zero_mem_preCantorSet (n : Nat) : 0 in preCantorSet n := by
  induction n with
  | zero =>
    simp [preCantorSet]
  | succ n ih =>
    exact Or.inl ⟨0, ih, by simp only [zero_div]⟩

/--
theorem `zero_mem_cantorSet` / 定理 `zero_mem_cantorSet`

English:
theorem zero_mem_cantorSet
  statement: 0 in cantorSet
  proof: by simp [cantorSet, zero_mem_preCantorSet]

中文:
定理 zero_mem_cantorSet
  结论: 0 in cantorSet
  证明: by simp [cantorSet, zero_mem_preCantorSet]

Depends on / 依赖: cantorSet, zero_mem_preCantorSet
-/
theorem zero_mem_cantorSet : 0 in cantorSet := by simp [cantorSet, zero_mem_preCantorSet]

/--
theorem `preCantorSet_antitone` / 定理 `preCantorSet_antitone`

English:
theorem preCantorSet_antitone
  statement: Antitone preCantorSet
  proof: by
  refine antitone_nat_of_succ_le fun m => ?_
  induction m with grind [preCantorSet_zero, preCantorSet_succ]

中文:
定理 preCantorSet_antitone
  结论: Antitone preCantorSet
  证明: by
  refine antitone_nat_of_succ_le fun m => ?_
  induction m with grind [preCantorSet_zero, preCantorSet_succ]

Depends on / 依赖: antitone_nat_of_succ_le, preCantorSet_succ, preCantorSet_zero
-/
theorem preCantorSet_antitone : Antitone preCantorSet := by
  refine antitone_nat_of_succ_le fun m => ?_
  induction m with grind [preCantorSet_zero, preCantorSet_succ]

/--
lemma `preCantorSet_subset_unitInterval` / 引理 `preCantorSet_subset_unitInterval`

English:
lemma preCantorSet_subset_unitInterval
  given: {n : Nat}
  statement: preCantorSet n subseteq Set.Icc 0 1
  proof: by
  rw [← preCantorSet_zero]
  exact preCantorSet_antitone (by simp)

中文:
引理 preCantorSet_subset_unitInterval
  条件: {n : 自然数}
  结论: preCantorSet n subseteq Set.Icc 0 1
  证明: by
  rw [← preCantorSet_zero]
  exact preCantorSet_antitone (by simp)

Depends on / 依赖: preCantorSet_antitone, preCantorSet_zero
-/
lemma preCantorSet_subset_unitInterval {n : Nat} : preCantorSet n subseteq Set.Icc 0 1 := by
  rw [← preCantorSet_zero]
  exact preCantorSet_antitone (by simp)

/--
lemma `cantorSet_subset_unitInterval` / 引理 `cantorSet_subset_unitInterval`

English:
lemma cantorSet_subset_unitInterval
  statement: cantorSet subseteq Set.Icc 0 1
  proof: Set.iInter_subset _ 0

中文:
引理 cantorSet_subset_unitInterval
  结论: cantorSet subseteq Set.Icc 0 1
  证明: Set.iInter_subset _ 0

Depends on / 依赖: Set.iInter_subset, iInter_subset
-/
lemma cantorSet_subset_unitInterval : cantorSet subseteq Set.Icc 0 1 :=
  Set.iInter_subset _ 0

/--
theorem `cantorSet_eq_union_halves` / 定理 `cantorSet_eq_union_halves`

English:
theorem cantorSet_eq_union_halves
  proof: by
  simp only [cantorSet]
  rw [Set.image_iInter]; rw [Set.image_iInter]
  rotate_left
  · exact (mulRight_bijective₀ 3⁻¹ (by simp)).comp (AddGroup.addLeft_bijective 2)
  · exact mulRight_bijective₀ 3⁻¹ (by simp)
  simp_rw [← Function.comp_def,
    ← Set.iInter_union_of_antitone
      (Set.monotone

中文:
定理 cantorSet_eq_union_halves
  证明: by
  simp only [cantorSet]
  rw [Set.image_iInter]; rw [Set.image_iInter]
  rotate_left
  · exact (mulRight_bijective₀ 3⁻¹ (by simp)).comp (AddGroup.addLeft_bijective 2)
  · exact mulRight_bijective₀ 3⁻¹ (by simp)
  simp_rw [← Function.comp_def,
    ← Set.iInter_union_of_antitone
      (Set.monotone

Depends on / 依赖: AddGroup, AddGroup.addLeft_bijective, Function, Function.comp_def, Set.iInter_union_of_antitone, Set.image_iInter, Set.monotone_image.comp_antitone, addLeft_bijective, cantorSet, comp_antitone, comp_def, iInter_nat_add, iInter_union_of_antitone, image_iInter, monotone_image, preCantorSet_antitone, preCantorSet_antitone.iInter_nat_add, preCantorSet_succ, rotate_left, simp_rw
-/
theorem cantorSet_eq_union_halves :
    cantorSet = (· / 3) '' cantorSet union (fun x => (2 + x) / 3) '' cantorSet := by
  simp only [cantorSet]
  rw [Set.image_iInter]; rw [Set.image_iInter]
  rotate_left
  · exact (mulRight_bijective₀ 3⁻¹ (by simp)).comp (AddGroup.addLeft_bijective 2)
  · exact mulRight_bijective₀ 3⁻¹ (by simp)
  simp_rw [← Function.comp_def,
    ← Set.iInter_union_of_antitone
      (Set.monotone_image.comp_antitone preCantorSet_antitone)
      (Set.monotone_image.comp_antitone preCantorSet_antitone),
    Function.comp_def, ← preCantorSet_succ]
  exact (preCantorSet_antitone.iInter_nat_add _).symm

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isClosed_preCantorSet` / 引理 `isClosed_preCantorSet`

English:
lemma isClosed_preCantorSet
  given: (n : Nat)
  statement: IsClosed (preCantorSet n)
  proof: by
  let f := Homeomorph.mulLeft₀ (1 / 3 : Real) (by simp)
  let g := (Homeomorph.addLeft (2 : Real)).trans f
  induction n with
  | zero => exact isClosed_Icc
  | succ n ih =>
    refine IsClosed.union ?_ ?_
    · simpa [f, div_eq_inv_mul] using f.isClosedEmbedding.isClosed_iff_image_isClosed.mp ih

中文:
引理 isClosed_preCantorSet
  条件: (n : 自然数)
  结论: IsClosed (preCantorSet n)
  证明: by
  let f := Homeomorph.mulLeft₀ (1 / 3 : Real) (by simp)
  let g := (Homeomorph.addLeft (2 : Real)).trans f
  induction n with
  | zero => exact isClosed_Icc
  | succ n ih =>
    refine IsClosed.union ?_ ?_
    · simpa [f, div_eq_inv_mul] using f.isClosedEmbedding.isClosed_iff_image_isClosed.mp ih

Depends on / 依赖: Homeomorph, Homeomorph.addLeft, Homeomorph.mulLeft, IsClosed, IsClosed.union, addLeft, div_eq_inv_mul, f.isClosedEmbedding.isClosed_iff_image_isClosed.mp, g.isClosedEmbedding.isClosed_iff_image_isClosed.mp, isClosedEmbedding, isClosed_Icc, isClosed_iff_image_isClosed
-/
lemma isClosed_preCantorSet (n : Nat) : IsClosed (preCantorSet n) := by
  let f := Homeomorph.mulLeft₀ (1 / 3 : Real) (by simp)
  let g := (Homeomorph.addLeft (2 : Real)).trans f
  induction n with
  | zero => exact isClosed_Icc
  | succ n ih =>
    refine IsClosed.union ?_ ?_
    · simpa [f, div_eq_inv_mul] using f.isClosedEmbedding.isClosed_iff_image_isClosed.mp ih
    · simpa [g, f, div_eq_inv_mul] using g.isClosedEmbedding.isClosed_iff_image_isClosed.mp ih

/--
lemma `isClosed_cantorSet` / 引理 `isClosed_cantorSet`

English:
lemma isClosed_cantorSet
  statement: IsClosed cantorSet
  proof: isClosed_iInter isClosed_preCantorSet

中文:
引理 isClosed_cantorSet
  结论: IsClosed cantorSet
  证明: isClosed_iInter isClosed_preCantorSet

Depends on / 依赖: isClosed_iInter, isClosed_preCantorSet
-/
lemma isClosed_cantorSet : IsClosed cantorSet :=
  isClosed_iInter isClosed_preCantorSet

/--
lemma `isCompact_cantorSet` / 引理 `isCompact_cantorSet`

English:
lemma isCompact_cantorSet
  statement: IsCompact cantorSet
  proof: isCompact_Icc.of_isClosed_subset isClosed_cantorSet cantorSet_subset_unitInterval

中文:
引理 isCompact_cantorSet
  结论: IsCompact cantorSet
  证明: isCompact_Icc.of_isClosed_subset isClosed_cantorSet cantorSet_subset_unitInterval

Depends on / 依赖: cantorSet_subset_unitInterval, isClosed_cantorSet, isCompact_Icc, isCompact_Icc.of_isClosed_subset, of_isClosed_subset
-/
lemma isCompact_cantorSet : IsCompact cantorSet :=
  isCompact_Icc.of_isClosed_subset isClosed_cantorSet cantorSet_subset_unitInterval

/-!
## The Cantor set as the set of 0–2 numbers in the ternary system.
-/

section ternary02

open Real

/--
theorem `ofDigits_zero_two_sequence_mem_cantorSet` / 定理 `ofDigits_zero_two_sequence_mem_cantorSet`

English:
theorem ofDigits_zero_two_sequence_mem_cantorSet
  statement: {a : Nat -> Fin 3}
  proof: by
  simp only [cantorSet, Set.mem_iInter]
  intro i
  induction i generalizing a with
  | zero =>
    simp only [preCantorSet_zero, Set.mem_Icc]
    exact ⟨ofDigits_nonneg a, ofDigits_le_one a⟩
  | succ i ih =>
    simp only [preCantorSet, Set.mem_union, Set.mem_image, ← exists_or]
    use ofDigits

中文:
定理 ofDigits_zero_two_sequence_mem_cantorSet
  结论: {a : 自然数 -> Fin 3}
  证明: by
  simp only [cantorSet, Set.mem_iInter]
  intro i
  induction i generalizing a with
  | zero =>
    simp only [preCantorSet_zero, Set.mem_Icc]
    exact ⟨ofDigits_nonneg a, ofDigits_le_one a⟩
  | succ i ih =>
    simp only [preCantorSet, Set.mem_union, Set.mem_image, ← exists_or]
    use ofDigits

Depends on / 依赖: Finset, Finset.range_one, Finset.sum_singleton, Nat.cast_ofNat, Set.mem_Icc, Set.mem_iInter, Set.mem_image, Set.mem_union, cantorSet, cast_ofNat, exists_or, generalizing, mem_Icc, mem_iInter, mem_image, mem_union, ofDigits, ofDigitsTerm, ofDigits_eq_sum_add_ofDigits, ofDigits_le_one
-/
theorem ofDigits_zero_two_sequence_mem_cantorSet {a : Nat -> Fin 3}
    (h : forall n, a n != 1) : ofDigits a in cantorSet := by
  simp only [cantorSet, Set.mem_iInter]
  intro i
  induction i generalizing a with
  | zero =>
    simp only [preCantorSet_zero, Set.mem_Icc]
    exact ⟨ofDigits_nonneg a, ofDigits_le_one a⟩
  | succ i ih =>
    simp only [preCantorSet, Set.mem_union, Set.mem_image, ← exists_or]
    use ofDigits (fun i => a (i + 1))
    have : (ofDigits fun i => a (i + 1)) in preCantorSet i := ih (by solve_by_elim)
    simp only [this, ofDigits_eq_sum_add_ofDigits a 1, Finset.range_one, ofDigitsTerm,
      Nat.cast_ofNat, Finset.sum_singleton, zero_add, pow_one, true_and, field]
    specialize h 0
    generalize a 0 = x at h
    fin_cases x <;> simp at ⊢ h

/--
theorem `ofDigits_zero_two_sequence_unique` / 定理 `ofDigits_zero_two_sequence_unique`

English:
theorem ofDigits_zero_two_sequence_unique
  statement: {a b : Nat -> Fin 3} (ha : forall n, a n != 1) (hb : forall n, b n != 1)
  proof: by
  by_contra! h
  rw [Function.ne_iff] at h
  let n0 := Nat.find h
  have h1 (n) (hn : n < n0) : a n = b n := by simpa using Nat.find_min h hn
  have h2 : a n0 != b n0 := by simpa using Nat.find_spec h
  generalize n0 = n1 at h1 h2
  clear h n0
  wlog h3 : a n1 = 0 ∧ b n1 = 2 generalizing a b
  · 

中文:
定理 ofDigits_zero_two_sequence_unique
  结论: {a b : 自然数 -> Fin 3} (ha : 对任意 n, a n != 1) (hb : 对任意 n, b n != 1)
  证明: by
  by_contra! h
  rw [Function.ne_iff] at h
  let n0 := Nat.find h
  have h1 (n) (hn : n < n0) : a n = b n := by simpa using Nat.find_min h hn
  have h2 : a n0 != b n0 := by simpa using Nat.find_spec h
  generalize n0 = n1 at h1 h2
  clear h n0
  wlog h3 : a n1 = 0 ∧ b n1 = 2 generalizing a b
  · 

Depends on / 依赖: Finset, Finset.range, Finset.sum_c, Function, Function.ne_iff, Nat.find, Nat.find_min, Nat.find_spec, find_min, find_spec, generalize, generalizing, h.symm, h2.symm, ne_iff, ofDigitsTerm, sum_c
-/
theorem ofDigits_zero_two_sequence_unique {a b : Nat -> Fin 3} (ha : forall n, a n != 1) (hb : forall n, b n != 1)
    (h : ofDigits a = ofDigits b) :
    a = b := by
  by_contra! h
  rw [Function.ne_iff] at h
  let n0 := Nat.find h
  have h1 (n) (hn : n < n0) : a n = b n := by simpa using Nat.find_min h hn
  have h2 : a n0 != b n0 := by simpa using Nat.find_spec h
  generalize n0 = n1 at h1 h2
  clear h n0
  wlog h3 : a n1 = 0 ∧ b n1 = 2 generalizing a b
  · exact this hb ha h.symm (fun n hn => (h1 n hn).symm) h2.symm (by grind)
  obtain ⟨h3, h4⟩ := h3
  clear h2
  have : ∑ x in Finset.range n1, ofDigitsTerm a x = ∑ x in Finset.range n1, ofDigitsTerm b x := by
    apply Finset.sum_congr rfl
    grind [ofDigitsTerm]
  rw [ofDigits_eq_sum_add_ofDigits a (n1 + 1)]; rw [ofDigits_eq_sum_add_ofDigits b (n1 + 1)]; rw [Finset.sum_range_succ]; rw [Finset.sum_range_succ]; rw [this] at h
  replace h : ofDigitsTerm a n1 + (3⁻¹ ^ n1 * ofDigits fun i => a (1 + n1 + i)) * (1 / 3) =
      (3⁻¹ ^ n1 * ofDigits fun i => b (1 + n1 + i)) * (1 / 3) + ofDigitsTerm b n1 := by
    ring_nf at h
    linarith
  simp only [ofDigitsTerm, h3, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, CharP.cast_eq_zero,
    Nat.cast_ofNat, pow_succ, mul_inv_rev, zero_mul, inv_pow, one_div, zero_add, h4,
    Nat.mod_succ] at h
  replace h : (ofDigits fun i => a (1 + n1 + i)) * 3⁻¹ =
      (ofDigits fun i => b (1 + n1 + i)) * 3⁻¹ + 2 * 3⁻¹ := by
    rw [← mul_right_inj' (show ((3 : Real) ^ n1)⁻¹ != 0 by positivity)]
    linarith
  linarith [ofDigits_nonneg (fun i => b (1 + n1 + i)), ofDigits_le_one (fun i => a (1 + n1 + i))]

/--
Definition of `cantorStep` / `cantorStep` 的定义

English:
definition cantorStep
  signature: (x : Real)
  body: if x in Set.Icc 0 (1 / 3) then
    3 * x
  else
    3 * x - 2

中文:
定义 cantorStep
  签名: (x : 实数)
  定义体: if x in Set.Icc 0 (1 / 3) then
    3 * x
  else
    3 * x - 2

Depends on / 依赖: Set.Icc
-/
noncomputable def cantorStep (x : Real) : Real :=
  if x in Set.Icc 0 (1 / 3) then
    3 * x
  else
    3 * x - 2

/--
theorem `cantorStep_mem_cantorSet` / 定理 `cantorStep_mem_cantorSet`

English:
theorem cantorStep_mem_cantorSet
  given: {x : Real} (hx : x in cantorSet)
  statement: cantorStep x in cantorSet
  proof: by
  simp only [cantorStep]
  obtain ⟨y, hy, rfl | rfl⟩ : exists y in cantorSet, y / 3 = x ∨ (2 + y) / 3 = x := by
    rw [cantorSet_eq_union_halves] at hx
    grind
  all_goals
    grind [cantorSet_subset_unitInterval]

中文:
定理 cantorStep_mem_cantorSet
  条件: {x : 实数} (hx : x in cantorSet)
  结论: cantorStep x in cantorSet
  证明: by
  simp only [cantorStep]
  obtain ⟨y, hy, rfl | rfl⟩ : exists y in cantorSet, y / 3 = x ∨ (2 + y) / 3 = x := by
    rw [cantorSet_eq_union_halves] at hx
    grind
  all_goals
    grind [cantorSet_subset_unitInterval]

Depends on / 依赖: all_goals, cantorSet, cantorSet_eq_union_halves, cantorSet_subset_unitInterval, cantorStep
-/
theorem cantorStep_mem_cantorSet {x : Real} (hx : x in cantorSet) : cantorStep x in cantorSet := by
  simp only [cantorStep]
  obtain ⟨y, hy, rfl | rfl⟩ : exists y in cantorSet, y / 3 = x ∨ (2 + y) / 3 = x := by
    rw [cantorSet_eq_union_halves] at hx
    grind
  all_goals
    grind [cantorSet_subset_unitInterval]

/--
Definition of `cantorSequence` / `cantorSequence` 的定义

English:
definition cantorSequence
  signature: (x : Real)
  body: Stream'.iterate cantorStep x

中文:
定义 cantorSequence
  签名: (x : 实数)
  定义体: Stream'.iterate cantorStep x

Depends on / 依赖: Stream, cantorStep, iterate
-/
noncomputable def cantorSequence (x : Real) : Stream' Real :=
  Stream'.iterate cantorStep x

/--
theorem `cantorSequence_mem_cantorSet` / 定理 `cantorSequence_mem_cantorSet`

English:
theorem cantorSequence_mem_cantorSet
  given: {x : Real} (hx : x in cantorSet) (n : Nat)
  proof: by
  induction n with
  | zero => simpa [cantorSequence]
  | succ n ih => exact cantorStep_mem_cantorSet ih

中文:
定理 cantorSequence_mem_cantorSet
  条件: {x : 实数} (hx : x in cantorSet) (n : 自然数)
  证明: by
  induction n with
  | zero => simpa [cantorSequence]
  | succ n ih => exact cantorStep_mem_cantorSet ih

Depends on / 依赖: cantorSequence, cantorStep_mem_cantorSet
-/
theorem cantorSequence_mem_cantorSet {x : Real} (hx : x in cantorSet) (n : Nat) :
    (cantorSequence x).get n in cantorSet := by
  induction n with
  | zero => simpa [cantorSequence]
  | succ n ih => exact cantorStep_mem_cantorSet ih

/--
Definition of `cantorToBinary` / `cantorToBinary` 的定义

English:
definition cantorToBinary
  signature: (x : Real)
  body: (cantorSequence x).map fun x =>
    if x in Set.Icc 0 (1 / 3) then
      false
    else
      true

中文:
定义 cantorToBinary
  签名: (x : 实数)
  定义体: (cantorSequence x).map fun x =>
    if x in Set.Icc 0 (1 / 3) then
      false
    else
      true

Depends on / 依赖: Set.Icc, cantorSequence
-/
noncomputable def cantorToBinary (x : Real) : Stream' Bool :=
  (cantorSequence x).map fun x =>
    if x in Set.Icc 0 (1 / 3) then
      false
    else
      true

/--
Definition of `cantorToTernary` / `cantorToTernary` 的定义

English:
definition cantorToTernary
  signature: (x : Real)
  body: (cantorToBinary x).map (cond · 2 0)

中文:
定义 cantorToTernary
  签名: (x : 实数)
  定义体: (cantorToBinary x).map (cond · 2 0)

Depends on / 依赖: cantorToBinary
-/
noncomputable def cantorToTernary (x : Real) : Stream' (Fin 3) :=
  (cantorToBinary x).map (cond · 2 0)

/--
theorem `ofDigits_bool_to_fin_three_mem_cantorSet` / 定理 `ofDigits_bool_to_fin_three_mem_cantorSet`

English:
theorem ofDigits_bool_to_fin_three_mem_cantorSet
  given: (f : Nat -> Bool)
  proof: ofDigits_zero_two_sequence_mem_cantorSet (by grind)

中文:
定理 ofDigits_bool_to_fin_three_mem_cantorSet
  条件: (f : 自然数 -> 布尔)
  证明: ofDigits_zero_two_sequence_mem_cantorSet (by grind)

Depends on / 依赖: ofDigits_zero_two_sequence_mem_cantorSet
-/
theorem ofDigits_bool_to_fin_three_mem_cantorSet (f : Nat -> Bool) :
    ofDigits (fun i => cond (f i) (2 : Fin 3) 0) in cantorSet :=
  ofDigits_zero_two_sequence_mem_cantorSet (by grind)

/--
theorem `cantorToTernary_ne_one` / 定理 `cantorToTernary_ne_one`

English:
theorem cantorToTernary_ne_one
  given: {x : Real} {n : Nat}
  statement: (cantorToTernary x).get n != 1
  proof: by
  grind [cantorToTernary, Stream'.get_map]

中文:
定理 cantorToTernary_ne_one
  条件: {x : 实数} {n : 自然数}
  结论: (cantorToTernary x).get n != 1
  证明: by
  grind [cantorToTernary, Stream'.get_map]

Depends on / 依赖: Stream, cantorToTernary, get_map
-/
theorem cantorToTernary_ne_one {x : Real} {n : Nat} : (cantorToTernary x).get n != 1 := by
  grind [cantorToTernary, Stream'.get_map]

/--
theorem `cantorSequence_get_succ` / 定理 `cantorSequence_get_succ`

English:
theorem cantorSequence_get_succ
  given: (x : Real) (n : Nat)
  proof: by
  simp only [cantorSequence, ofDigitsTerm, cantorToTernary, cantorToBinary, Set.mem_Icc,
    Bool.if_true_right, Bool.or_false, Stream'.get_map, Bool.cond_not, Bool.cond_decide,
    Stream'.get_succ_iterate', cantorStep]
  split_ifs <;> simp
  field

中文:
定理 cantorSequence_get_succ
  条件: (x : 实数) (n : 自然数)
  证明: by
  simp only [cantorSequence, ofDigitsTerm, cantorToTernary, cantorToBinary, Set.mem_Icc,
    Bool.if_true_right, Bool.or_false, Stream'.get_map, Bool.cond_not, Bool.cond_decide,
    Stream'.get_succ_iterate', cantorStep]
  split_ifs <;> simp
  field

Depends on / 依赖: Bool.cond_decide, Bool.cond_not, Bool.if_true_right, Bool.or_false, Set.mem_Icc, Stream, cantorSequence, cantorStep, cantorToBinary, cantorToTernary, cond_decide, cond_not, get_map, get_succ_iterate, if_true_right, mem_Icc, ofDigitsTerm, or_false, split_ifs
-/
theorem cantorSequence_get_succ (x : Real) (n : Nat) :
    (cantorSequence x).get (n + 1) =
      3 * ((cantorSequence x).get n - 3 ^ n * ofDigitsTerm (cantorToTernary x).get n) := by
  simp only [cantorSequence, ofDigitsTerm, cantorToTernary, cantorToBinary, Set.mem_Icc,
    Bool.if_true_right, Bool.or_false, Stream'.get_map, Bool.cond_not, Bool.cond_decide,
    Stream'.get_succ_iterate', cantorStep]
  split_ifs <;> simp
  field

/--
theorem `cantorSequence_eq_self_sub_sum_cantorToTernary` / 定理 `cantorSequence_eq_self_sub_sum_cantorToTernary`

English:
theorem cantorSequence_eq_self_sub_sum_cantorToTernary
  given: (x : Real) (n : Nat)
  proof: by
  induction n with
  | zero => simp [cantorSequence]
  | succ n ih => rw [cantorSequence_get_succ, ih, Finset.sum_range_succ]; ring

中文:
定理 cantorSequence_eq_self_sub_sum_cantorToTernary
  条件: (x : 实数) (n : 自然数)
  证明: by
  induction n with
  | zero => simp [cantorSequence]
  | succ n ih => rw [cantorSequence_get_succ, ih, Finset.sum_range_succ]; ring

Depends on / 依赖: Finset, Finset.sum_range_succ, cantorSequence, cantorSequence_get_succ, sum_range_succ
-/
theorem cantorSequence_eq_self_sub_sum_cantorToTernary (x : Real) (n : Nat) :
    (cantorSequence x).get n =
    (x - ∑ i in Finset.range n, ofDigitsTerm (cantorToTernary x).get i) * 3 ^ n := by
  induction n with
  | zero => simp [cantorSequence]
  | succ n ih => rw [cantorSequence_get_succ, ih, Finset.sum_range_succ]; ring

/--
theorem `ofDigits_cantorToTernary_sum_le` / 定理 `ofDigits_cantorToTernary_sum_le`

English:
theorem ofDigits_cantorToTernary_sum_le
  given: {x : Real} (hx : x in cantorSet) {n : Nat}
  proof: by
  have h_mem := cantorSequence_mem_cantorSet hx n
  rw [cantorSequence_eq_self_sub_sum_cantorToTernary x n] at h_mem
  apply cantorSet_subset_unitInterval at h_mem
  simp only [Set.mem_Icc] at h_mem
  simpa using! h_mem.left

中文:
定理 ofDigits_cantorToTernary_sum_le
  条件: {x : 实数} (hx : x in cantorSet) {n : 自然数}
  证明: by
  have h_mem := cantorSequence_mem_cantorSet hx n
  rw [cantorSequence_eq_self_sub_sum_cantorToTernary x n] at h_mem
  apply cantorSet_subset_unitInterval at h_mem
  simp only [Set.mem_Icc] at h_mem
  simpa using! h_mem.left

Depends on / 依赖: Set.mem_Icc, cantorSequence_eq_self_sub_sum_cantorToTernary, cantorSequence_mem_cantorSet, cantorSet_subset_unitInterval, h_mem, h_mem.left, mem_Icc
-/
theorem ofDigits_cantorToTernary_sum_le {x : Real} (hx : x in cantorSet) {n : Nat} :
    ∑ i in Finset.range n, ofDigitsTerm (cantorToTernary x) i <= x := by
  have h_mem := cantorSequence_mem_cantorSet hx n
  rw [cantorSequence_eq_self_sub_sum_cantorToTernary x n] at h_mem
  apply cantorSet_subset_unitInterval at h_mem
  simp only [Set.mem_Icc] at h_mem
  simpa using! h_mem.left

/--
theorem `le_ofDigits_cantorToTernary_sum` / 定理 `le_ofDigits_cantorToTernary_sum`

English:
theorem le_ofDigits_cantorToTernary_sum
  given: {x : Real} (hx : x in cantorSet) {n : Nat}
  proof: by
  have h_mem := cantorSequence_mem_cantorSet hx n
  rw [cantorSequence_eq_self_sub_sum_cantorToTernary x n] at h_mem
  apply cantorSet_subset_unitInterval at h_mem
  simp only [Set.mem_Icc] at h_mem
  rw [← mul_le_mul_iff_left₀ (show 0 < (3 : Real) ^ n by positivity)]; rw [sub_mul]; rw [inv_pow];

中文:
定理 le_ofDigits_cantorToTernary_sum
  条件: {x : 实数} (hx : x in cantorSet) {n : 自然数}
  证明: by
  have h_mem := cantorSequence_mem_cantorSet hx n
  rw [cantorSequence_eq_self_sub_sum_cantorToTernary x n] at h_mem
  apply cantorSet_subset_unitInterval at h_mem
  simp only [Set.mem_Icc] at h_mem
  rw [← mul_le_mul_iff_left₀ (show 0 < (3 : Real) ^ n by positivity)]; rw [sub_mul]; rw [inv_pow];

Depends on / 依赖: Set.mem_Icc, cantorSequence_eq_self_sub_sum_cantorToTernary, cantorSequence_mem_cantorSet, cantorSet_subset_unitInterval, h_mem, inv_pow, mem_Icc, sub_mul
-/
theorem le_ofDigits_cantorToTernary_sum {x : Real} (hx : x in cantorSet) {n : Nat} :
    x - (3⁻¹ : Real) ^ n <= ∑ i in Finset.range n, ofDigitsTerm (cantorToTernary x) i := by
  have h_mem := cantorSequence_mem_cantorSet hx n
  rw [cantorSequence_eq_self_sub_sum_cantorToTernary x n] at h_mem
  apply cantorSet_subset_unitInterval at h_mem
  simp only [Set.mem_Icc] at h_mem
  rw [← mul_le_mul_iff_left₀ (show 0 < (3 : Real) ^ n by positivity)]; rw [sub_mul]; rw [inv_pow]; rw [inv_mul_cancel₀ (by simp)]
  linarith!

/--
theorem `ofDigits_cantorToTernary` / 定理 `ofDigits_cantorToTernary`

English:
theorem ofDigits_cantorToTernary
  given: {x : Real} (hx : x in cantorSet)
  proof: by
  simp only [ofDigits]
  rw [HasSum.tsum_eq]
  rw [hasSum_iff_tendsto_nat_of_summable_norm]
  swap
  · simpa only [norm_of_nonneg ofDigitsTerm_nonneg] using summable_ofDigitsTerm
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n => x - (3⁻¹ : Real) ^ n) (h := fun _ => x)
  · rw [← ten

中文:
定理 ofDigits_cantorToTernary
  条件: {x : 实数} (hx : x in cantorSet)
  证明: by
  simp only [ofDigits]
  rw [HasSum.tsum_eq]
  rw [hasSum_iff_tendsto_nat_of_summable_norm]
  swap
  · simpa only [norm_of_nonneg ofDigitsTerm_nonneg] using summable_ofDigitsTerm
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n => x - (3⁻¹ : Real) ^ n) (h := fun _ => x)
  · rw [← ten

Depends on / 依赖: HasSum, HasSum.tsum_eq, hasSum_iff_tendsto_nat_of_summable_norm, le_ofDigits_, norm_of_nonneg, ofDigits, ofDigitsTerm_nonneg, sub_sub_cancel_left, summable_ofDigitsTerm, tendsto_const_nhds, tendsto_of_tendsto_of_tendsto_of_le_of_le, tendsto_pow_atTop_nhds_zero_of_abs_lt_one, tendsto_sub_nhds_zero_iff, tsum_eq
-/
theorem ofDigits_cantorToTernary {x : Real} (hx : x in cantorSet) :
    ofDigits (cantorToTernary x).get = x := by
  simp only [ofDigits]
  rw [HasSum.tsum_eq]
  rw [hasSum_iff_tendsto_nat_of_summable_norm]
  swap
  · simpa only [norm_of_nonneg ofDigitsTerm_nonneg] using summable_ofDigitsTerm
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n => x - (3⁻¹ : Real) ^ n) (h := fun _ => x)
  · rw [← tendsto_sub_nhds_zero_iff]
    simp only [sub_sub_cancel_left]
    rw [show 0 = -(0 : Real) by simp]
    exact (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)).neg
  · exact tendsto_const_nhds
  · exact fun _ => le_ofDigits_cantorToTernary_sum hx
  · exact fun _ => ofDigits_cantorToTernary_sum_le hx

/--
theorem `cantorSet_eq_zero_two_ofDigits` / 定理 `cantorSet_eq_zero_two_ofDigits`

English:
theorem cantorSet_eq_zero_two_ofDigits
  proof: by
  ext x
  refine ⟨fun h => ?_, fun ⟨a, ha⟩ => ?_⟩
  · use cantorToTernary x
    exact ⟨fun _ => cantorToTernary_ne_one, ofDigits_cantorToTernary h⟩
  · rw [← ha.right]
    exact ofDigits_zero_two_sequence_mem_cantorSet ha.left

中文:
定理 cantorSet_eq_zero_two_ofDigits
  证明: by
  ext x
  refine ⟨fun h => ?_, fun ⟨a, ha⟩ => ?_⟩
  · use cantorToTernary x
    exact ⟨fun _ => cantorToTernary_ne_one, ofDigits_cantorToTernary h⟩
  · rw [← ha.right]
    exact ofDigits_zero_two_sequence_mem_cantorSet ha.left

Depends on / 依赖: cantorToTernary, cantorToTernary_ne_one, ha.left, ha.right, ofDigits_cantorToTernary, ofDigits_zero_two_sequence_mem_cantorSet
-/
theorem cantorSet_eq_zero_two_ofDigits :
    cantorSet = {x | exists a : Nat -> Fin 3, (forall i, a i != 1) ∧ ofDigits a = x} := by
  ext x
  refine ⟨fun h => ?_, fun ⟨a, ha⟩ => ?_⟩
  · use cantorToTernary x
    exact ⟨fun _ => cantorToTernary_ne_one, ofDigits_cantorToTernary h⟩
  · rw [← ha.right]
    exact ofDigits_zero_two_sequence_mem_cantorSet ha.left

end ternary02

/-!
## The Cantor set is homeomorphic to `ℕ → Bool`
-/

open Real

/--
Definition of `cantorSetEquivNatToBool` / `cantorSetEquivNatToBool` 的定义

English:
definition cantorSetEquivNatToBool
  signature: : cantorSet ≃ (Nat -> Bool) where
  body: fun ⟨x, h⟩ => (cantorToBinary x).get
  invFun (y : Nat -> Bool) :=
    ⟨ofDigits (fun i => cond (y i) 2 0), ofDigits_bool_to_fin_three_mem_cantorSet y⟩
  left_inv := by
    intro ⟨x, hx⟩
    simp only [Fin.isValue, Subtype.mk.injEq]
    exact ofDigits_cantorToTernary hx
  right_inv := by
    intro y

中文:
定义 cantorSetEquivNatToBool
  签名: : cantorSet ≃ (自然数 -> 布尔) where
  定义体: fun ⟨x, h⟩ => (cantorToBinary x).get
  invFun (y : Nat -> Bool) :=
    ⟨ofDigits (fun i => cond (y i) 2 0), ofDigits_bool_to_fin_three_mem_cantorSet y⟩
  left_inv := by
    intro ⟨x, hx⟩
    simp only [Fin.isValue, Subtype.mk.injEq]
    exact ofDigits_cantorToTernary hx
  right_inv := by
    intro y

Depends on / 依赖: cantorToBinary
-/
noncomputable def cantorSetEquivNatToBool : cantorSet ≃ (Nat -> Bool) where
  toFun := fun ⟨x, h⟩ => (cantorToBinary x).get
  invFun (y : Nat -> Bool) :=
    ⟨ofDigits (fun i => cond (y i) 2 0), ofDigits_bool_to_fin_three_mem_cantorSet y⟩
  left_inv := by
    intro ⟨x, hx⟩
    simp only [Fin.isValue, Subtype.mk.injEq]
    exact ofDigits_cantorToTernary hx
  right_inv := by
    intro y
    simp only [Fin.isValue]
    set x := @ofDigits 3 (fun i => cond (y i) 2 0)
    have := ofDigits_cantorToTernary (ofDigits_bool_to_fin_three_mem_cantorSet y)
    apply ofDigits_zero_two_sequence_unique at this
    rotate_left
    · exact fun n => cantorToTernary_ne_one
    · grind
    ext n
    apply congrFun (a := n) at this
    grind [cantorToTernary, Stream'.get_map]

/--
Definition of `cantorSetHomeomorphNatToBool` / `cantorSetHomeomorphNatToBool` 的定义

English:
definition cantorSetHomeomorphNatToBool
  signature: : cantorSet ≃ₜ (Nat -> Bool)
  body: Homeomorph.symm Continuous.homeoOfEquivCompactToT2 (f := cantorSetEquivNatToBool.symm)
    (Continuous.subtype_mk (Continuous.comp continuous_ofDigits (by fun_prop)) _)

中文:
定义 cantorSetHomeomorphNatToBool
  签名: : cantorSet ≃ₜ (自然数 -> 布尔)
  定义体: Homeomorph.symm Continuous.homeoOfEquivCompactToT2 (f := cantorSetEquivNatToBool.symm)
    (Continuous.subtype_mk (Continuous.comp continuous_ofDigits (by fun_prop)) _)

Depends on / 依赖: Continuous, Continuous.comp, Continuous.homeoOfEquivCompactToT2, Continuous.subtype_mk, Homeomorph, Homeomorph.symm, cantorSetEquivNatToBool, cantorSetEquivNatToBool.symm, continuous_ofDigits, fun_prop, homeoOfEquivCompactToT2, subtype_mk
-/
noncomputable def cantorSetHomeomorphNatToBool : cantorSet ≃ₜ (Nat -> Bool) :=
Homeomorph.symm Continuous.homeoOfEquivCompactToT2 (f := cantorSetEquivNatToBool.symm)
    (Continuous.subtype_mk (Continuous.comp continuous_ofDigits (by fun_prop)) _)

/--
Definition of `cantorSpaceHomeomorphNatToCantorSpace` / `cantorSpaceHomeomorphNatToCantorSpace` 的定义

English:
definition cantorSpaceHomeomorphNatToCantorSpace
  signature: : (Nat -> Bool) ≃ₜ (Nat -> Nat -> Bool)
  body: (Homeomorph.piCongrLeft Nat.pairEquiv.symm).trans Homeomorph.piCurry

中文:
定义 cantorSpaceHomeomorphNatToCantorSpace
  签名: : (自然数 -> 布尔) ≃ₜ (自然数 -> 自然数 -> 布尔)
  定义体: (Homeomorph.piCongrLeft Nat.pairEquiv.symm).trans Homeomorph.piCurry

Depends on / 依赖: Homeomorph, Homeomorph.piCongrLeft, Homeomorph.piCurry, Nat.pairEquiv.symm, pairEquiv, piCongrLeft, piCurry
-/
def cantorSpaceHomeomorphNatToCantorSpace : (Nat -> Bool) ≃ₜ (Nat -> Nat -> Bool) :=
  (Homeomorph.piCongrLeft Nat.pairEquiv.symm).trans Homeomorph.piCurry
