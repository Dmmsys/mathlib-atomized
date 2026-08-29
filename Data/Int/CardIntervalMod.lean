/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Count
public import Mathlib.Data.Rat.Floor
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Counting elements in an interval with given residue

The theorems in this file generalise `Nat.card_multiples` in
`Mathlib/Data/Nat/Factorization/Basic.lean` to all integer intervals and any fixed residue (not just
zero, which reduces to the multiples). Theorems are given for `Ico` and `Ioc` intervals.
-/

public section


open Finset Int

namespace Int

variable (a b : Int) {r : Int}


/--
lemma `Ico_filter_modEq_eq` / 引理 `Ico_filter_modEq_eq`

English:
lemma Ico_filter_modEq_eq
  given: (v : Int)
  proof: by
  ext x
  simp_rw [mem_map, mem_filter, mem_Ico, Function.Embedding.coeFn_mk, ← eq_sub_iff_add_eq,
    exists_eq_right, modEq_comm, modEq_iff_dvd, sub_lt_sub_iff_right, sub_le_sub_iff_right]

中文:
引理 Ico_filter_modEq_eq
  条件: (v : 整数)
  证明: by
  ext x
  simp_rw [mem_map, mem_filter, mem_Ico, Function.Embedding.coeFn_mk, ← eq_sub_iff_add_eq,
    exists_eq_right, modEq_comm, modEq_iff_dvd, sub_lt_sub_iff_right, sub_le_sub_iff_right]

Depends on / 依赖: Embedding, Function, Function.Embedding.coeFn_mk, coeFn_mk, eq_sub_iff_add_eq, exists_eq_right, mem_Ico, mem_filter, mem_map, modEq_comm, modEq_iff_dvd, simp_rw, sub_le_sub_iff_right, sub_lt_sub_iff_right
-/
lemma Ico_filter_modEq_eq (v : Int) :
    {x in Ico a b | x ≡ v [ZMOD r]} =
    {x in Ico (a - v) (b - v) | r ∣ x}.map ⟨(· + v), add_left_injective v⟩ := by
  ext x
  simp_rw [mem_map, mem_filter, mem_Ico, Function.Embedding.coeFn_mk, ← eq_sub_iff_add_eq,
    exists_eq_right, modEq_comm, modEq_iff_dvd, sub_lt_sub_iff_right, sub_le_sub_iff_right]

/--
lemma `Ioc_filter_modEq_eq` / 引理 `Ioc_filter_modEq_eq`

English:
lemma Ioc_filter_modEq_eq
  given: (v : Int)
  proof: by
  ext x
  simp_rw [mem_map, mem_filter, mem_Ioc, Function.Embedding.coeFn_mk, ← eq_sub_iff_add_eq,
    exists_eq_right, modEq_comm, modEq_iff_dvd, sub_lt_sub_iff_right, sub_le_sub_iff_right]

中文:
引理 Ioc_filter_modEq_eq
  条件: (v : 整数)
  证明: by
  ext x
  simp_rw [mem_map, mem_filter, mem_Ioc, Function.Embedding.coeFn_mk, ← eq_sub_iff_add_eq,
    exists_eq_right, modEq_comm, modEq_iff_dvd, sub_lt_sub_iff_right, sub_le_sub_iff_right]

Depends on / 依赖: Embedding, Function, Function.Embedding.coeFn_mk, coeFn_mk, eq_sub_iff_add_eq, exists_eq_right, mem_Ioc, mem_filter, mem_map, modEq_comm, modEq_iff_dvd, simp_rw, sub_le_sub_iff_right, sub_lt_sub_iff_right
-/
lemma Ioc_filter_modEq_eq (v : Int) :
    {x in Ioc a b | x ≡ v [ZMOD r]} =
    {x in Ioc (a - v) (b - v) | r ∣ x}.map ⟨(· + v), add_left_injective v⟩ := by
  ext x
  simp_rw [mem_map, mem_filter, mem_Ioc, Function.Embedding.coeFn_mk, ← eq_sub_iff_add_eq,
    exists_eq_right, modEq_comm, modEq_iff_dvd, sub_lt_sub_iff_right, sub_le_sub_iff_right]

variable (hr : 0 < r)
include hr

/--
lemma `Ico_filter_dvd_eq` / 引理 `Ico_filter_dvd_eq`

English:
lemma Ico_filter_dvd_eq
  proof: by
  ext x
  simp only [mem_map, mem_filter, mem_Ico, ceil_le, lt_ceil, div_le_iff₀, lt_div_iff₀,
    dvd_iff_exists_eq_mul_left, cast_pos.2 hr, ← cast_mul, cast_lt, cast_le]
  aesop

中文:
引理 Ico_filter_dvd_eq
  证明: by
  ext x
  simp only [mem_map, mem_filter, mem_Ico, ceil_le, lt_ceil, div_le_iff₀, lt_div_iff₀,
    dvd_iff_exists_eq_mul_left, cast_pos.2 hr, ← cast_mul, cast_lt, cast_le]
  aesop

Depends on / 依赖: cast_le, cast_lt, cast_mul, cast_pos, ceil_le, dvd_iff_exists_eq_mul_left, lt_ceil, mem_Ico, mem_filter, mem_map
-/
lemma Ico_filter_dvd_eq :
    {x in Ico a b | r ∣ x} =
      (Ico ⌈a / (r : Rat)⌉ ⌈b / (r : Rat)⌉).map ⟨(· * r), mul_left_injective₀ hr.ne'⟩ := by
  ext x
  simp only [mem_map, mem_filter, mem_Ico, ceil_le, lt_ceil, div_le_iff₀, lt_div_iff₀,
    dvd_iff_exists_eq_mul_left, cast_pos.2 hr, ← cast_mul, cast_lt, cast_le]
  aesop

/--
lemma `Ioc_filter_dvd_eq` / 引理 `Ioc_filter_dvd_eq`

English:
lemma Ioc_filter_dvd_eq
  proof: by
  ext x
  simp only [mem_map, mem_filter, mem_Ioc, floor_lt, le_floor, div_lt_iff₀, le_div_iff₀,
    dvd_iff_exists_eq_mul_left, cast_pos.2 hr, ← cast_mul, cast_lt, cast_le]
  aesop

中文:
引理 Ioc_filter_dvd_eq
  证明: by
  ext x
  simp only [mem_map, mem_filter, mem_Ioc, floor_lt, le_floor, div_lt_iff₀, le_div_iff₀,
    dvd_iff_exists_eq_mul_left, cast_pos.2 hr, ← cast_mul, cast_lt, cast_le]
  aesop

Depends on / 依赖: cast_le, cast_lt, cast_mul, cast_pos, dvd_iff_exists_eq_mul_left, floor_lt, le_floor, mem_Ioc, mem_filter, mem_map
-/
lemma Ioc_filter_dvd_eq :
    {x in Ioc a b | r ∣ x} =
      (Ioc ⌊a / (r : Rat)⌋ ⌊b / (r : Rat)⌋).map ⟨(· * r), mul_left_injective₀ hr.ne'⟩ := by
  ext x
  simp only [mem_map, mem_filter, mem_Ioc, floor_lt, le_floor, div_lt_iff₀, le_div_iff₀,
    dvd_iff_exists_eq_mul_left, cast_pos.2 hr, ← cast_mul, cast_lt, cast_le]
  aesop

/--
theorem `Ico_filter_dvd_card` / 定理 `Ico_filter_dvd_card`

English:
theorem Ico_filter_dvd_card
  statement: #{x in Ico a b | r ∣ x} = max (⌈b / (r : Rat)⌉ - ⌈a / (r : Rat)⌉) 0
  proof: by
  rw [Ico_filter_dvd_eq _ _ hr]; rw [card_map]; rw [card_Ico]; rw [toNat_eq_max]

中文:
定理 Ico_filter_dvd_card
  结论: #{x in Ico a b | r ∣ x} = max (⌈b / (r : Rat)⌉ - ⌈a / (r : Rat)⌉) 0
  证明: by
  rw [Ico_filter_dvd_eq _ _ hr]; rw [card_map]; rw [card_Ico]; rw [toNat_eq_max]

Depends on / 依赖: Ico_filter_dvd_eq, card_Ico, card_map, toNat_eq_max
-/
theorem Ico_filter_dvd_card : #{x in Ico a b | r ∣ x} = max (⌈b / (r : Rat)⌉ - ⌈a / (r : Rat)⌉) 0 := by
  rw [Ico_filter_dvd_eq _ _ hr]; rw [card_map]; rw [card_Ico]; rw [toNat_eq_max]

/--
theorem `Ioc_filter_dvd_card` / 定理 `Ioc_filter_dvd_card`

English:
theorem Ioc_filter_dvd_card
  statement: #{x in Ioc a b | r ∣ x} = max (⌊b / (r : Rat)⌋ - ⌊a / (r : Rat)⌋) 0
  proof: by
  rw [Ioc_filter_dvd_eq _ _ hr]; rw [card_map]; rw [card_Ioc]; rw [toNat_eq_max]

中文:
定理 Ioc_filter_dvd_card
  结论: #{x in Ioc a b | r ∣ x} = max (⌊b / (r : Rat)⌋ - ⌊a / (r : Rat)⌋) 0
  证明: by
  rw [Ioc_filter_dvd_eq _ _ hr]; rw [card_map]; rw [card_Ioc]; rw [toNat_eq_max]

Depends on / 依赖: Ioc_filter_dvd_eq, card_Ioc, card_map, toNat_eq_max
-/
theorem Ioc_filter_dvd_card : #{x in Ioc a b | r ∣ x} = max (⌊b / (r : Rat)⌋ - ⌊a / (r : Rat)⌋) 0 := by
  rw [Ioc_filter_dvd_eq _ _ hr]; rw [card_map]; rw [card_Ioc]; rw [toNat_eq_max]

/--
theorem `Ico_filter_modEq_card` / 定理 `Ico_filter_modEq_card`

English:
theorem Ico_filter_modEq_card
  given: (v : Int)
  proof: by
  simp [Ico_filter_modEq_eq, Ico_filter_dvd_eq, hr]

中文:
定理 Ico_filter_modEq_card
  条件: (v : 整数)
  证明: by
  simp [Ico_filter_modEq_eq, Ico_filter_dvd_eq, hr]

Depends on / 依赖: Ico_filter_dvd_eq, Ico_filter_modEq_eq
-/
theorem Ico_filter_modEq_card (v : Int) :
    #{x in Ico a b | x ≡ v [ZMOD r]} = max (⌈(b - v) / (r : Rat)⌉ - ⌈(a - v) / (r : Rat)⌉) 0 := by
  simp [Ico_filter_modEq_eq, Ico_filter_dvd_eq, hr]

/--
theorem `Ioc_filter_modEq_card` / 定理 `Ioc_filter_modEq_card`

English:
theorem Ioc_filter_modEq_card
  given: (v : Int)
  proof: by
  simp [Ioc_filter_modEq_eq, Ioc_filter_dvd_eq, hr]

中文:
定理 Ioc_filter_modEq_card
  条件: (v : 整数)
  证明: by
  simp [Ioc_filter_modEq_eq, Ioc_filter_dvd_eq, hr]

Depends on / 依赖: Ioc_filter_dvd_eq, Ioc_filter_modEq_eq
-/
theorem Ioc_filter_modEq_card (v : Int) :
    #{x in Ioc a b | x ≡ v [ZMOD r]} = max (⌊(b - v) / (r : Rat)⌋ - ⌊(a - v) / (r : Rat)⌋) 0 := by
  simp [Ioc_filter_modEq_eq, Ioc_filter_dvd_eq, hr]

end Int

namespace Nat

variable (a b : Nat) {r : Nat}

/--
lemma `Ico_filter_modEq_cast` / 引理 `Ico_filter_modEq_cast`

English:
lemma Ico_filter_modEq_cast
  given: {v : Nat}
  proof: by
  ext x
  simp only [mem_map, mem_filter, mem_Ico, castEmbedding_apply]
  constructor
  · simp_rw [forall_exists_index, ← natCast_modEq_iff]; intro y ⟨h, c⟩; subst c; exact_mod_cast h
  · intro h; lift x to Nat using (by omega); exact ⟨x, by simp_all [natCast_modEq_iff]⟩

中文:
引理 Ico_filter_modEq_cast
  条件: {v : 自然数}
  证明: by
  ext x
  simp only [mem_map, mem_filter, mem_Ico, castEmbedding_apply]
  constructor
  · simp_rw [forall_exists_index, ← natCast_modEq_iff]; intro y ⟨h, c⟩; subst c; exact_mod_cast h
  · intro h; lift x to Nat using (by omega); exact ⟨x, by simp_all [natCast_modEq_iff]⟩

Depends on / 依赖: castEmbedding_apply, forall_exists_index, mem_Ico, mem_filter, mem_map, natCast_modEq_iff, simp_rw
-/
lemma Ico_filter_modEq_cast {v : Nat} :
    {x in Ico a b | x ≡ v [MOD r]}.map castEmbedding =
      {x in Ico (a : Int) (b : Int) | x ≡ v [ZMOD r]} := by
  ext x
  simp only [mem_map, mem_filter, mem_Ico, castEmbedding_apply]
  constructor
  · simp_rw [forall_exists_index, ← natCast_modEq_iff]; intro y ⟨h, c⟩; subst c; exact_mod_cast h
  · intro h; lift x to Nat using (by omega); exact ⟨x, by simp_all [natCast_modEq_iff]⟩

/--
lemma `Ioc_filter_modEq_cast` / 引理 `Ioc_filter_modEq_cast`

English:
lemma Ioc_filter_modEq_cast
  given: {v : Nat}
  proof: by
  ext x
  simp only [mem_map, mem_filter, mem_Ioc, castEmbedding_apply]
  constructor
  · simp_rw [forall_exists_index, ← natCast_modEq_iff]; intro y ⟨h, c⟩; subst c; exact_mod_cast h
  · intro h; lift x to Nat using (by lia); exact ⟨x, by simp_all [natCast_modEq_iff]⟩

中文:
引理 Ioc_filter_modEq_cast
  条件: {v : 自然数}
  证明: by
  ext x
  simp only [mem_map, mem_filter, mem_Ioc, castEmbedding_apply]
  constructor
  · simp_rw [forall_exists_index, ← natCast_modEq_iff]; intro y ⟨h, c⟩; subst c; exact_mod_cast h
  · intro h; lift x to Nat using (by lia); exact ⟨x, by simp_all [natCast_modEq_iff]⟩

Depends on / 依赖: castEmbedding_apply, forall_exists_index, mem_Ioc, mem_filter, mem_map, natCast_modEq_iff, simp_rw
-/
lemma Ioc_filter_modEq_cast {v : Nat} :
    {x in Ioc a b | x ≡ v [MOD r]}.map castEmbedding =
      {x in Ioc (a : Int) (b : Int) | x ≡ v [ZMOD r]} := by
  ext x
  simp only [mem_map, mem_filter, mem_Ioc, castEmbedding_apply]
  constructor
  · simp_rw [forall_exists_index, ← natCast_modEq_iff]; intro y ⟨h, c⟩; subst c; exact_mod_cast h
  · intro h; lift x to Nat using (by lia); exact ⟨x, by simp_all [natCast_modEq_iff]⟩

variable (hr : 0 < r)
include hr

/--
theorem `Ico_filter_modEq_card` / 定理 `Ico_filter_modEq_card`

English:
theorem Ico_filter_modEq_card
  given: (v : Nat)
  proof: by
  simp_rw [← Ico_filter_modEq_cast _ _ ▸ card_map _,
    Int.Ico_filter_modEq_card _ _ (cast_lt.mpr hr), Int.cast_natCast]

中文:
定理 Ico_filter_modEq_card
  条件: (v : 自然数)
  证明: by
  simp_rw [← Ico_filter_modEq_cast _ _ ▸ card_map _,
    Int.Ico_filter_modEq_card _ _ (cast_lt.mpr hr), Int.cast_natCast]

Depends on / 依赖: Ico_filter_modEq_card, Ico_filter_modEq_cast, Int.Ico_filter_modEq_card, Int.cast_natCast, card_map, cast_lt, cast_lt.mpr, cast_natCast, simp_rw
-/
theorem Ico_filter_modEq_card (v : Nat) :
    #{x in Ico a b | x ≡ v [MOD r]} = max (⌈(b - v) / (r : Rat)⌉ - ⌈(a - v) / (r : Rat)⌉) 0 := by
  simp_rw [← Ico_filter_modEq_cast _ _ ▸ card_map _,
    Int.Ico_filter_modEq_card _ _ (cast_lt.mpr hr), Int.cast_natCast]

/--
theorem `Ioc_filter_modEq_card` / 定理 `Ioc_filter_modEq_card`

English:
theorem Ioc_filter_modEq_card
  given: (v : Nat)
  proof: by
  simp_rw [← Ioc_filter_modEq_cast _ _ ▸ card_map _,
    Int.Ioc_filter_modEq_card _ _ (cast_lt.mpr hr), Int.cast_natCast]

中文:
定理 Ioc_filter_modEq_card
  条件: (v : 自然数)
  证明: by
  simp_rw [← Ioc_filter_modEq_cast _ _ ▸ card_map _,
    Int.Ioc_filter_modEq_card _ _ (cast_lt.mpr hr), Int.cast_natCast]

Depends on / 依赖: Int.Ioc_filter_modEq_card, Int.cast_natCast, Ioc_filter_modEq_card, Ioc_filter_modEq_cast, card_map, cast_lt, cast_lt.mpr, cast_natCast, simp_rw
-/
theorem Ioc_filter_modEq_card (v : Nat) :
    #{x in Ioc a b | x ≡ v [MOD r]} = max (⌊(b - v) / (r : Rat)⌋ - ⌊(a - v) / (r : Rat)⌋) 0 := by
  simp_rw [← Ioc_filter_modEq_cast _ _ ▸ card_map _,
    Int.Ioc_filter_modEq_card _ _ (cast_lt.mpr hr), Int.cast_natCast]

/--
theorem `count_modEq_card_eq_ceil` / 定理 `count_modEq_card_eq_ceil`

English:
theorem count_modEq_card_eq_ceil
  given: (v : Nat)
  proof: by
  have hr' : 0 < (r : Rat) := by positivity
  rw [count_eq_card_filter_range]; rw [← Ico_zero_eq_range]; rw [Ico_filter_modEq_card _ _ hr]; rw [max_eq_left (sub_nonneg.mpr <| by gcongr; positivity)]
  conv_lhs =>
    rw [← div_add_mod v r]; rw [cast_add]; rw [cast_mul]; rw [add_comm]
    tactic =

中文:
定理 count_modEq_card_eq_ceil
  条件: (v : 自然数)
  证明: by
  have hr' : 0 < (r : Rat) := by positivity
  rw [count_eq_card_filter_range]; rw [← Ico_zero_eq_range]; rw [Ico_filter_modEq_card _ _ hr]; rw [max_eq_left (sub_nonneg.mpr <| by gcongr; positivity)]
  conv_lhs =>
    rw [← div_add_mod v r]; rw [cast_add]; rw [cast_mul]; rw [add_comm]
    tactic =

Depends on / 依赖: Ico_filter_modEq_card, Ico_zero_eq_range, Int.ceil_sub_natCast, Set.mem_Ioc, add_comm, cast_add, cast_mul, cast_zero, ceil_eq_zero_iff, ceil_sub_natCast, conv_lhs, count_eq_card_filter_range, div_add_mod, max_eq_left, mem_Ioc, simp_rw, sub_div, sub_eq_self, sub_nonneg, sub_nonneg.mpr
-/
theorem count_modEq_card_eq_ceil (v : Nat) :
    b.count (· ≡ v [MOD r]) = ⌈(b - (v % r : Nat)) / (r : Rat)⌉ := by
  have hr' : 0 < (r : Rat) := by positivity
  rw [count_eq_card_filter_range]; rw [← Ico_zero_eq_range]; rw [Ico_filter_modEq_card _ _ hr]; rw [max_eq_left (sub_nonneg.mpr <| by gcongr; positivity)]
  conv_lhs =>
    rw [← div_add_mod v r]; rw [cast_add]; rw [cast_mul]; rw [add_comm]
    tactic => simp_rw [← sub_sub, sub_div (_ - _), mul_div_cancel_left₀ _ hr'.ne',
      Int.ceil_sub_natCast]
    rw [sub_sub_sub_cancel_right]; rw [cast_zero]; rw [zero_sub]
  rw [sub_eq_self]; rw [ceil_eq_zero_iff]; rw [Set.mem_Ioc]; rw [div_le_iff₀ hr']; rw [lt_div_iff₀ hr']; rw [neg_one_mul]; rw [zero_mul]; rw [neg_lt_neg_iff]; rw [cast_lt]
  exact ⟨mod_lt _ hr, by simp⟩

/--
theorem `count_modEq_card` / 定理 `count_modEq_card`

English:
theorem count_modEq_card
  given: (v : Nat)
  proof: by
  have hr' : 0 < (r : Rat) := by positivity
  rw [← ofNat_inj]; rw [count_modEq_card_eq_ceil _ hr]; rw [cast_add]
  conv_lhs => rw [← div_add_mod b r, cast_add, cast_mul, ← add_sub, _root_.add_div,
    mul_div_cancel_left₀ _ hr'.ne', add_comm, Int.ceil_add_natCast, add_comm]
  rw [add_right_inj]


中文:
定理 count_modEq_card
  条件: (v : 自然数)
  证明: by
  have hr' : 0 < (r : Rat) := by positivity
  rw [← ofNat_inj]; rw [count_modEq_card_eq_ceil _ hr]; rw [cast_add]
  conv_lhs => rw [← div_add_mod b r, cast_add, cast_mul, ← add_sub, _root_.add_div,
    mul_div_cancel_left₀ _ hr'.ne', add_comm, Int.ceil_add_natCast, add_comm]
  rw [add_right_inj]


Depends on / 依赖: Int.cast_one, Int.ceil_add_natCast, Int.ceil_eq_iff, _root_, _root_.add_div, add_comm, add_div, add_right_inj, add_sub, cast_add, cast_le, cast_mul, cast_one, cast_pos, cast_sub, ceil_add_natCast, ceil_eq_iff, conv_lhs, count_modEq_card_eq_ceil, div_add_mod
-/
theorem count_modEq_card (v : Nat) :
    b.count (· ≡ v [MOD r]) = b / r + if v % r < b % r then 1 else 0 := by
  have hr' : 0 < (r : Rat) := by positivity
  rw [← ofNat_inj]; rw [count_modEq_card_eq_ceil _ hr]; rw [cast_add]
  conv_lhs => rw [← div_add_mod b r, cast_add, cast_mul, ← add_sub, _root_.add_div,
    mul_div_cancel_left₀ _ hr'.ne', add_comm, Int.ceil_add_natCast, add_comm]
  rw [add_right_inj]
  split_ifs with h
  · rw [← cast_sub h.le, Int.ceil_eq_iff, div_le_iff₀ hr', lt_div_iff₀ hr', cast_one, Int.cast_one,
      sub_self, zero_mul, cast_pos, tsub_pos_iff_lt, one_mul, cast_le, tsub_le_iff_right]
    exact ⟨h, ((mod_lt _ hr).trans_le (by simp)).le⟩
  · rw [cast_zero, ceil_eq_zero_iff, Set.mem_Ioc, div_le_iff₀ hr', lt_div_iff₀ hr', zero_mul,
      tsub_nonpos, ← neg_eq_neg_one_mul, neg_lt_sub_iff_lt_add, ← cast_add, cast_lt, cast_le]
    exact ⟨(mod_lt _ hr).trans_le (by simp), not_lt.mp h⟩

end Nat
