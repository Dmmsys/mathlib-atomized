/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Embedding
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Order.Interval.Finset.Basic

/-!
# Finite intervals of integers

This file proves that `ℤ` is a `LocallyFiniteOrder` and calculates the cardinality of its
intervals as finsets and fintypes.
-/

public section

assert_not_exists Field

open Finset Int

namespace Int

/--
Instance `instLocallyFiniteOrder` / 实例 `instLocallyFiniteOrder`

English:
instance instLocallyFiniteOrder
  signature: : LocallyFiniteOrder Int where
  body: (Finset.range (b + 1 - a).toNat).map Nat.castEmbedding.trans addLeftEmbedding a
finsetIco a b := (Finset.range (b - a).toNat).map Nat.castEmbedding.trans addLeftEmbedding a
  finsetIoc a b :=
(Finset.range (b - a).toNat).map Nat.castEmbedding.trans addLeftEmbedding (a + 1)
  finsetIoo a b :=
(Finset

中文:
实例 instLocallyFiniteOrder
  签名: : LocallyFiniteOrder 整数 where
  定义体: (Finset.range (b + 1 - a).toNat).map Nat.castEmbedding.trans addLeftEmbedding a
finsetIco a b := (Finset.range (b - a).toNat).map Nat.castEmbedding.trans addLeftEmbedding a
  finsetIoc a b :=
(Finset.range (b - a).toNat).map Nat.castEmbedding.trans addLeftEmbedding (a + 1)
  finsetIoo a b :=
(Finset

Depends on / 依赖: Embedding, Finset, Finset.range, Function, Function.Embedding.trans_apply, Nat.castEmbedding.trans, Nat.castEmbedding_apply, addLeftEmbed, addLeftEmbedding, castEmbedding, castEmbedding_apply, finsetIco, finsetIoc, finsetIoo, finset_mem_Icc, mem_map, mem_range, simp_rw, trans_apply
-/
instance instLocallyFiniteOrder : LocallyFiniteOrder Int where
  finsetIcc a b :=
(Finset.range (b + 1 - a).toNat).map Nat.castEmbedding.trans addLeftEmbedding a
finsetIco a b := (Finset.range (b - a).toNat).map Nat.castEmbedding.trans addLeftEmbedding a
  finsetIoc a b :=
(Finset.range (b - a).toNat).map Nat.castEmbedding.trans addLeftEmbedding (a + 1)
  finsetIoo a b :=
(Finset.range (b - a - 1).toNat).map Nat.castEmbedding.trans addLeftEmbedding (a + 1)
  finset_mem_Icc a b x := by
    simp_rw [mem_map, mem_range, Function.Embedding.trans_apply, Nat.castEmbedding_apply,
      addLeftEmbedding_apply]
    constructor
    · lia
    · intro
      use (x - a).toNat
      lia
  finset_mem_Ico a b x := by
    simp_rw [mem_map, mem_range, Function.Embedding.trans_apply, Nat.castEmbedding_apply,
      addLeftEmbedding_apply]
    constructor
    · lia
    · intro
      use (x - a).toNat
      lia
  finset_mem_Ioc a b x := by
    simp_rw [mem_map, mem_range, Function.Embedding.trans_apply, Nat.castEmbedding_apply,
      addLeftEmbedding_apply]
    constructor
    · lia
    · intro
      use (x - (a + 1)).toNat
      lia
  finset_mem_Ioo a b x := by
    simp_rw [mem_map, mem_range, Function.Embedding.trans_apply, Nat.castEmbedding_apply,
      addLeftEmbedding_apply]
    constructor
    · lia
    · intro
      use (x - (a + 1)).toNat
      lia

variable (a b : Int)

/--
theorem `Icc_eq_finset_map` / 定理 `Icc_eq_finset_map`

English:
theorem Icc_eq_finset_map
  proof: rfl

中文:
定理 Icc_eq_finset_map
  证明: rfl
-/
theorem Icc_eq_finset_map :
    Icc a b =
      (Finset.range (b + 1 - a).toNat).map (Nat.castEmbedding.trans <| addLeftEmbedding a) :=
  rfl

/--
theorem `Ico_eq_finset_map` / 定理 `Ico_eq_finset_map`

English:
theorem Ico_eq_finset_map
  proof: rfl

中文:
定理 Ico_eq_finset_map
  证明: rfl
-/
theorem Ico_eq_finset_map :
    Ico a b = (Finset.range (b - a).toNat).map (Nat.castEmbedding.trans <| addLeftEmbedding a) :=
  rfl

/--
theorem `Ioc_eq_finset_map` / 定理 `Ioc_eq_finset_map`

English:
theorem Ioc_eq_finset_map
  proof: rfl

中文:
定理 Ioc_eq_finset_map
  证明: rfl
-/
theorem Ioc_eq_finset_map :
    Ioc a b =
      (Finset.range (b - a).toNat).map (Nat.castEmbedding.trans <| addLeftEmbedding (a + 1)) :=
  rfl

/--
theorem `Ioo_eq_finset_map` / 定理 `Ioo_eq_finset_map`

English:
theorem Ioo_eq_finset_map
  proof: rfl

中文:
定理 Ioo_eq_finset_map
  证明: rfl
-/
theorem Ioo_eq_finset_map :
    Ioo a b =
      (Finset.range (b - a - 1).toNat).map (Nat.castEmbedding.trans <| addLeftEmbedding (a + 1)) :=
  rfl

/--
theorem `uIcc_eq_finset_map` / 定理 `uIcc_eq_finset_map`

English:
theorem uIcc_eq_finset_map
  proof: rfl

@[simp]

中文:
定理 uIcc_eq_finset_map
  证明: rfl

@[simp]
-/
theorem uIcc_eq_finset_map :
    uIcc a b = (range (max a b + 1 - min a b).toNat).map
      (Nat.castEmbedding.trans <| addLeftEmbedding <| min a b) := rfl

@[simp]
/--
theorem `card_Icc` / 定理 `card_Icc`

English:
theorem card_Icc
  statement: #(Icc a b) = (b + 1 - a).toNat
  proof: (card_map _).trans card_range _

@[simp]

中文:
定理 card_Icc
  结论: #(Icc a b) = (b + 1 - a).to自然数
  证明: (card_map _).trans card_range _

@[simp]

Depends on / 依赖: card_map, card_range
-/
theorem card_Icc : #(Icc a b) = (b + 1 - a).toNat := (card_map _).trans card_range _

@[simp]
/--
theorem `card_Ico` / 定理 `card_Ico`

English:
theorem card_Ico
  statement: #(Ico a b) = (b - a).toNat
  proof: (card_map _).trans card_range _

@[simp]

中文:
定理 card_Ico
  结论: #(Ico a b) = (b - a).to自然数
  证明: (card_map _).trans card_range _

@[simp]

Depends on / 依赖: card_map, card_range
-/
theorem card_Ico : #(Ico a b) = (b - a).toNat := (card_map _).trans card_range _

@[simp]
/--
theorem `card_Ioc` / 定理 `card_Ioc`

English:
theorem card_Ioc
  statement: #(Ioc a b) = (b - a).toNat
  proof: (card_map _).trans card_range _

@[simp]

中文:
定理 card_Ioc
  结论: #(Ioc a b) = (b - a).to自然数
  证明: (card_map _).trans card_range _

@[simp]

Depends on / 依赖: card_map, card_range
-/
theorem card_Ioc : #(Ioc a b) = (b - a).toNat := (card_map _).trans card_range _

@[simp]
/--
theorem `card_Ioo` / 定理 `card_Ioo`

English:
theorem card_Ioo
  statement: #(Ioo a b) = (b - a - 1).toNat
  proof: (card_map _).trans card_range _

@[simp]

中文:
定理 card_Ioo
  结论: #(Ioo a b) = (b - a - 1).to自然数
  证明: (card_map _).trans card_range _

@[simp]

Depends on / 依赖: card_map, card_range
-/
theorem card_Ioo : #(Ioo a b) = (b - a - 1).toNat := (card_map _).trans card_range _

@[simp]
/--
theorem `card_uIcc` / 定理 `card_uIcc`

English:
theorem card_uIcc
  statement: #(uIcc a b) = (b - a).natAbs + 1
  proof: (card_map _).trans
(Nat.cast_inj (R := Int)).mp by
      rw [card_range]; rw [Int.toNat_of_nonneg (sub_nonneg_of_le <| le_add_one min_le_max)]; rw [Int.natCast_add]; rw [Int.natCast_natAbs]; rw [add_comm]; rw [add_sub_assoc]; rw [max_sub_min_eq_abs]; rw [add_comm]; rw [Int.ofNat_one]

中文:
定理 card_uIcc
  结论: #(uIcc a b) = (b - a).natAbs + 1
  证明: (card_map _).trans
(Nat.cast_inj (R := Int)).mp by
      rw [card_range]; rw [Int.toNat_of_nonneg (sub_nonneg_of_le <| le_add_one min_le_max)]; rw [Int.natCast_add]; rw [Int.natCast_natAbs]; rw [add_comm]; rw [add_sub_assoc]; rw [max_sub_min_eq_abs]; rw [add_comm]; rw [Int.ofNat_one]

Depends on / 依赖: Int.natCast_add, Int.natCast_natAbs, Int.ofNat_one, Int.toNat_of_nonneg, Nat.cast_inj, add_comm, add_sub_assoc, card_map, card_range, cast_inj, le_add_one, max_sub_min_eq_abs, min_le_max, natCast_add, natCast_natAbs, ofNat_one, sub_nonneg_of_le, toNat_of_nonneg
-/
theorem card_uIcc : #(uIcc a b) = (b - a).natAbs + 1 :=
(card_map _).trans
(Nat.cast_inj (R := Int)).mp by
      rw [card_range]; rw [Int.toNat_of_nonneg (sub_nonneg_of_le <| le_add_one min_le_max)]; rw [Int.natCast_add]; rw [Int.natCast_natAbs]; rw [add_comm]; rw [add_sub_assoc]; rw [max_sub_min_eq_abs]; rw [add_comm]; rw [Int.ofNat_one]

/--
theorem `card_Icc_of_le` / 定理 `card_Icc_of_le`

English:
theorem card_Icc_of_le
  given: (h : a <= b + 1)
  statement: (#(Icc a b) : Int) = b + 1 - a
  proof: by
  rw [card_Icc]; rw [toNat_sub_of_le h]

中文:
定理 card_Icc_of_le
  条件: (h : a <= b + 1)
  结论: (#(Icc a b) : 整数) = b + 1 - a
  证明: by
  rw [card_Icc]; rw [toNat_sub_of_le h]

Depends on / 依赖: card_Icc, toNat_sub_of_le
-/
theorem card_Icc_of_le (h : a <= b + 1) : (#(Icc a b) : Int) = b + 1 - a := by
  rw [card_Icc]; rw [toNat_sub_of_le h]

/--
theorem `card_Ico_of_le` / 定理 `card_Ico_of_le`

English:
theorem card_Ico_of_le
  given: (h : a <= b)
  statement: (#(Ico a b) : Int) = b - a
  proof: by
  rw [card_Ico]; rw [toNat_sub_of_le h]

中文:
定理 card_Ico_of_le
  条件: (h : a <= b)
  结论: (#(Ico a b) : 整数) = b - a
  证明: by
  rw [card_Ico]; rw [toNat_sub_of_le h]

Depends on / 依赖: card_Ico, toNat_sub_of_le
-/
theorem card_Ico_of_le (h : a <= b) : (#(Ico a b) : Int) = b - a := by
  rw [card_Ico]; rw [toNat_sub_of_le h]

/--
theorem `card_Ioc_of_le` / 定理 `card_Ioc_of_le`

English:
theorem card_Ioc_of_le
  given: (h : a <= b)
  statement: (#(Ioc a b) : Int) = b - a
  proof: by
  rw [card_Ioc]; rw [toNat_sub_of_le h]

中文:
定理 card_Ioc_of_le
  条件: (h : a <= b)
  结论: (#(Ioc a b) : 整数) = b - a
  证明: by
  rw [card_Ioc]; rw [toNat_sub_of_le h]

Depends on / 依赖: card_Ioc, toNat_sub_of_le
-/
theorem card_Ioc_of_le (h : a <= b) : (#(Ioc a b) : Int) = b - a := by
  rw [card_Ioc]; rw [toNat_sub_of_le h]

/--
theorem `card_Ioo_of_lt` / 定理 `card_Ioo_of_lt`

English:
theorem card_Ioo_of_lt
  given: (h : a < b)
  statement: (#(Ioo a b) : Int) = b - a - 1
  proof: by
  rw [card_Ioo]; rw [sub_sub]; rw [toNat_sub_of_le h]

中文:
定理 card_Ioo_of_lt
  条件: (h : a < b)
  结论: (#(Ioo a b) : 整数) = b - a - 1
  证明: by
  rw [card_Ioo]; rw [sub_sub]; rw [toNat_sub_of_le h]

Depends on / 依赖: card_Ioo, sub_sub, toNat_sub_of_le
-/
theorem card_Ioo_of_lt (h : a < b) : (#(Ioo a b) : Int) = b - a - 1 := by
  rw [card_Ioo]; rw [sub_sub]; rw [toNat_sub_of_le h]

/--
theorem `Icc_eq_pair` / 定理 `Icc_eq_pair`

English:
theorem Icc_eq_pair
  statement: Finset.Icc a (a + 1) = {a, a + 1}
  proof: by
  ext
  simp
  omega

中文:
定理 Icc_eq_pair
  结论: Finset.Icc a (a + 1) = {a, a + 1}
  证明: by
  ext
  simp
  omega
-/
theorem Icc_eq_pair : Finset.Icc a (a + 1) = {a, a + 1} := by
  ext
  simp
  omega

/--
theorem `card_fintype_Icc_of_le` / 定理 `card_fintype_Icc_of_le`

English:
theorem card_fintype_Icc_of_le
  given: (h : a <= b + 1)
  statement: (Fintype.card (Set.Icc a b) : Int) = b + 1 - a
  proof: by
  simp [h]

中文:
定理 card_fintype_Icc_of_le
  条件: (h : a <= b + 1)
  结论: (Fintype.card (Set.Icc a b) : 整数) = b + 1 - a
  证明: by
  simp [h]
-/
theorem card_fintype_Icc_of_le (h : a <= b + 1) : (Fintype.card (Set.Icc a b) : Int) = b + 1 - a := by
  simp [h]

/--
theorem `card_fintype_Ico_of_le` / 定理 `card_fintype_Ico_of_le`

English:
theorem card_fintype_Ico_of_le
  given: (h : a <= b)
  statement: (Fintype.card (Set.Ico a b) : Int) = b - a
  proof: by
  simp [h]

中文:
定理 card_fintype_Ico_of_le
  条件: (h : a <= b)
  结论: (Fintype.card (Set.Ico a b) : 整数) = b - a
  证明: by
  simp [h]
-/
theorem card_fintype_Ico_of_le (h : a <= b) : (Fintype.card (Set.Ico a b) : Int) = b - a := by
  simp [h]

/--
theorem `card_fintype_Ioc_of_le` / 定理 `card_fintype_Ioc_of_le`

English:
theorem card_fintype_Ioc_of_le
  given: (h : a <= b)
  statement: (Fintype.card (Set.Ioc a b) : Int) = b - a
  proof: by
  simp [h]

中文:
定理 card_fintype_Ioc_of_le
  条件: (h : a <= b)
  结论: (Fintype.card (Set.Ioc a b) : 整数) = b - a
  证明: by
  simp [h]
-/
theorem card_fintype_Ioc_of_le (h : a <= b) : (Fintype.card (Set.Ioc a b) : Int) = b - a := by
  simp [h]

/--
theorem `card_fintype_Ioo_of_lt` / 定理 `card_fintype_Ioo_of_lt`

English:
theorem card_fintype_Ioo_of_lt
  given: (h : a < b)
  statement: (Fintype.card (Set.Ioo a b) : Int) = b - a - 1
  proof: by
  simp [h]

中文:
定理 card_fintype_Ioo_of_lt
  条件: (h : a < b)
  结论: (Fintype.card (Set.Ioo a b) : 整数) = b - a - 1
  证明: by
  simp [h]
-/
theorem card_fintype_Ioo_of_lt (h : a < b) : (Fintype.card (Set.Ioo a b) : Int) = b - a - 1 := by
  simp [h]

/--
theorem `image_Ico_emod` / 定理 `image_Ico_emod`

English:
theorem image_Ico_emod
  given: (n a : Int) (h : 0 <= a)
  statement: (Ico n (n + a)).image (· % a) = Ico 0 a
  proof: by
  obtain rfl | ha := eq_or_lt_of_le h
  · simp
  ext i
  simp only [mem_image, mem_Ico]
  constructor
  · rintro ⟨i, _, rfl⟩
    exact ⟨emod_nonneg i ha.ne', emod_lt_of_pos i ha⟩
  rintro ⟨hi₀, hia⟩
  have hn := Int.emod_add_mul_ediv n a
  obtain hi | hi := lt_or_ge i (n % a)
  · refine ⟨i + a * 

中文:
定理 image_Ico_emod
  条件: (n a : 整数) (h : 0 <= a)
  结论: (Ico n (n + a)).image (· % a) = Ico 0 a
  证明: by
  obtain rfl | ha := eq_or_lt_of_le h
  · simp
  ext i
  simp only [mem_image, mem_Ico]
  constructor
  · rintro ⟨i, _, rfl⟩
    exact ⟨emod_nonneg i ha.ne', emod_lt_of_pos i ha⟩
  rintro ⟨hi₀, hia⟩
  have hn := Int.emod_add_mul_ediv n a
  obtain hi | hi := lt_or_ge i (n % a)
  · refine ⟨i + a * 

Depends on / 依赖: Int.emod_add_mul_ediv, Int.emod_lt_of_pos, emod_add_mul_ediv, emod_lt_of_pos, emod_nonneg, eq_or_lt_of_le, ha.ne, lt_or_ge, mem_Ico, mem_image
-/
theorem image_Ico_emod (n a : Int) (h : 0 <= a) : (Ico n (n + a)).image (· % a) = Ico 0 a := by
  obtain rfl | ha := eq_or_lt_of_le h
  · simp
  ext i
  simp only [mem_image, mem_Ico]
  constructor
  · rintro ⟨i, _, rfl⟩
    exact ⟨emod_nonneg i ha.ne', emod_lt_of_pos i ha⟩
  rintro ⟨hi₀, hia⟩
  have hn := Int.emod_add_mul_ediv n a
  obtain hi | hi := lt_or_ge i (n % a)
  · refine ⟨i + a * (n / a + 1), ⟨?_, ?_⟩, ?_⟩
    · calc
        n = 0 + n % a + a * (n / a) := by simp [hn]
        _ <= i + a + a * (n / a) := by gcongr; exact (Int.emod_lt_of_pos n ha).le
        _ = i + a * (n / a + 1) := by grind
    · calc
        i + a * (n / a + 1) < n % a + a * (n / a + 1) := by gcongr
        _ = n + a := by rw [mul_add, mul_one, ← add_assoc, hn]
    · rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hi₀ hia]
  · refine ⟨i + a * (n / a), ⟨?_, ?_⟩, ?_⟩
    · exact hn.symm.le.trans (add_le_add_left hi _)
    · rw [add_comm n a]
      refine add_lt_add_of_lt_of_le hia (le_trans ?_ hn.le)
      simp only [le_add_iff_nonneg_left]
      exact Int.emod_nonneg n (ne_of_gt ha)
    · rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hi₀ hia]

end Int

section Nat

/--
lemma `Finset.Icc_succ_succ` / 引理 `Finset.Icc_succ_succ`

English:
lemma Finset.Icc_succ_succ
  given: (m n : Nat)
  proof: by
  ext
  simp only [mem_Icc, union_insert, union_singleton, mem_insert]
  omega

中文:
引理 Finset.Icc_succ_succ
  条件: (m n : 自然数)
  证明: by
  ext
  simp only [mem_Icc, union_insert, union_singleton, mem_insert]
  omega

Depends on / 依赖: mem_Icc, mem_insert, union_insert, union_singleton
-/
lemma Finset.Icc_succ_succ (m n : Nat) :
    Icc (-(m + 1) : Int) (n + 1) = Icc (-m : Int) n union {(-(m + 1) : Int), (n + 1 : Int)} := by
  ext
  simp only [mem_Icc, union_insert, union_singleton, mem_insert]
  omega

/--
lemma `Finset.Ico_succ_succ` / 引理 `Finset.Ico_succ_succ`

English:
lemma Finset.Ico_succ_succ
  given: (m n : Nat)
  proof: by
  ext
  simp only [mem_Ico, union_insert, union_singleton, mem_insert]
  omega

中文:
引理 Finset.Ico_succ_succ
  条件: (m n : 自然数)
  证明: by
  ext
  simp only [mem_Ico, union_insert, union_singleton, mem_insert]
  omega

Depends on / 依赖: mem_Ico, mem_insert, union_insert, union_singleton
-/
lemma Finset.Ico_succ_succ (m n : Nat) :
    Ico (-(m + 1) : Int) (n + 1) = Ico (-m : Int) n union {(-(m + 1) : Int), (n : Int)} := by
  ext
  simp only [mem_Ico, union_insert, union_singleton, mem_insert]
  omega

/--
lemma `Finset.Ioc_succ_succ` / 引理 `Finset.Ioc_succ_succ`

English:
lemma Finset.Ioc_succ_succ
  given: (m n : Nat)
  proof: by
  ext
  simp only [mem_Ioc, union_insert, union_singleton, mem_insert]
  lia

中文:
引理 Finset.Ioc_succ_succ
  条件: (m n : 自然数)
  证明: by
  ext
  simp only [mem_Ioc, union_insert, union_singleton, mem_insert]
  lia

Depends on / 依赖: mem_Ioc, mem_insert, union_insert, union_singleton
-/
lemma Finset.Ioc_succ_succ (m n : Nat) :
    Ioc (-(m + 1) : Int) (n + 1) = Ioc (-m : Int) n union {-(m : Int), (n + 1 : Int)} := by
  ext
  simp only [mem_Ioc, union_insert, union_singleton, mem_insert]
  lia

/--
lemma `Finset.Ioo_succ_succ` / 引理 `Finset.Ioo_succ_succ`

English:
lemma Finset.Ioo_succ_succ
  given: (m n : Nat)
  proof: by
  ext
  simp only [mem_Ioo, union_insert, union_singleton, mem_insert]
  lia

中文:
引理 Finset.Ioo_succ_succ
  条件: (m n : 自然数)
  证明: by
  ext
  simp only [mem_Ioo, union_insert, union_singleton, mem_insert]
  lia

Depends on / 依赖: mem_Ioo, mem_insert, union_insert, union_singleton
-/
lemma Finset.Ioo_succ_succ (m n : Nat) :
    Ioo (-(m + 1) : Int) (n + 1) = Ioo (-m : Int) n union {-(m : Int), (n : Int)} := by
  ext
  simp only [mem_Ioo, union_insert, union_singleton, mem_insert]
  lia

end Nat
