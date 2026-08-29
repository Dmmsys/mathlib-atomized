/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.Interval

/-!
# Sharp bounds for sums of bounded finsets of integers

The sum of a finset of integers with cardinality `s` where all elements are at most `c` can be given
a sharper upper bound than `#s * c`, because the elements are distinct.

This file provides these sharp bounds, both in the upper-bounded and analogous lower-bounded cases.
-/

public section


namespace Finset

/--
lemma `sum_le_sum_Ioc` / 引理 `sum_le_sum_Ioc`

English:
lemma sum_le_sum_Ioc
  given: {s : Finset Int} {c : Int} (hs : forall x in s, x <= c)
  proof: by
  set r := Ioc (c - #s) c
  calc
    _ <= ∑ x in s inter r, x + #(s \ r) • (c - #s) := by
      rw [← sum_inter_add_sum_sdiff s r _]
      gcongr
      apply sum_le_card_nsmul
      grind
    _ = ∑ x in r inter s, x + #(r \ s) • (c - #s) := by
      rw [inter_comm]; rw [card_sdiff_comm]
      rw 

中文:
引理 sum_le_sum_Ioc
  条件: {s : 有限集 整数} {c : 整数} (hs : 对任意 x in s, x <= c)
  证明: by
  set r := Ioc (c - #s) c
  calc
    _ <= ∑ x in s inter r, x + #(s \ r) • (c - #s) := by
      rw [← sum_inter_add_sum_sdiff s r _]
      gcongr
      apply sum_le_card_nsmul
      grind
    _ = ∑ x in r inter s, x + #(r \ s) • (c - #s) := by
      rw [inter_comm]; rw [card_sdiff_comm]
      rw 

Depends on / 依赖: Int.card_Ioc, Int.toNat_natCast, card_Ioc, card_nsmul_le_sum, card_sdiff_comm, inter_comm, mem_Ioc, mem_sdiff, sub_sub_cancel, sum_inter_add_sum_sdiff, sum_le_card_nsmul, toNat_natCast
-/
lemma sum_le_sum_Ioc {s : Finset Int} {c : Int} (hs : forall x in s, x <= c) :
    ∑ x in s, x <= ∑ x in Ioc (c - #s) c, x := by
  set r := Ioc (c - #s) c
  calc
    _ <= ∑ x in s inter r, x + #(s \ r) • (c - #s) := by
      rw [← sum_inter_add_sum_sdiff s r _]
      gcongr
      apply sum_le_card_nsmul
      grind
    _ = ∑ x in r inter s, x + #(r \ s) • (c - #s) := by
      rw [inter_comm]; rw [card_sdiff_comm]
      rw [Int.card_Ioc]; rw [sub_sub_cancel]; rw [Int.toNat_natCast]
    _ <= _ := by
      rw [← sum_inter_add_sum_sdiff r s _]
      gcongr
      refine card_nsmul_le_sum _ _ _ fun x mx => ?_
      rw [mem_sdiff]; rw [mem_Ioc] at mx; exact mx.1.1.le

/--
lemma `sum_le_sum_range` / 引理 `sum_le_sum_range`

English:
lemma sum_le_sum_range
  given: {s : Finset Int} {c : Int} (hs : forall x in s, x <= c)
  proof: by
  convert! sum_le_sum_Ioc hs
  refine sum_nbij (c - ·) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro x mx; rw [mem_Ioc]; rw [mem_range] at mx; lia
  · intro x mx y my (h : c - x = c - y); lia
  · intro x mx; simp_rw [coe_range, Set.mem_image, Set.mem_Iio]
    rw [mem_coe]; rw [mem_Ioc] at mx
    use (c - x

中文:
引理 sum_le_sum_range
  条件: {s : 有限集 整数} {c : 整数} (hs : 对任意 x in s, x <= c)
  证明: by
  convert! sum_le_sum_Ioc hs
  refine sum_nbij (c - ·) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro x mx; rw [mem_Ioc]; rw [mem_range] at mx; lia
  · intro x mx y my (h : c - x = c - y); lia
  · intro x mx; simp_rw [coe_range, Set.mem_image, Set.mem_Iio]
    rw [mem_coe]; rw [mem_Ioc] at mx
    use (c - x

Depends on / 依赖: Set.mem_Iio, Set.mem_image, coe_range, convert, mem_Iio, mem_Ioc, mem_coe, mem_image, mem_range, simp_rw, sum_le_sum_Ioc, sum_nbij
-/
lemma sum_le_sum_range {s : Finset Int} {c : Int} (hs : forall x in s, x <= c) :
    ∑ x in s, x <= ∑ n in range #s, (c - n) := by
  convert! sum_le_sum_Ioc hs
  refine sum_nbij (c - ·) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro x mx; rw [mem_Ioc]; rw [mem_range] at mx; lia
  · intro x mx y my (h : c - x = c - y); lia
  · intro x mx; simp_rw [coe_range, Set.mem_image, Set.mem_Iio]
    rw [mem_coe]; rw [mem_Ioc] at mx
    use (c - x).toNat; grind

/--
lemma `sum_Ico_le_sum` / 引理 `sum_Ico_le_sum`

English:
lemma sum_Ico_le_sum
  given: {s : Finset Int} {c : Int} (hs : forall x in s, c <= x)
  proof: by
  set r := Ico c (c + #s)
  calc
    _ <= ∑ x in r inter s, x + #(r \ s) • (c + #s) := by
      grw [← sum_inter_add_sum_sdiff r s, ← sum_le_card_nsmul _ _ _ fun x mx => ?_]
      rw [mem_sdiff]; rw [mem_Ico] at mx; exact mx.1.2.le
    _ = ∑ x in s inter r, x + #(s \ r) • (c + #s) := by
      rw 

中文:
引理 sum_Ico_le_sum
  条件: {s : 有限集 整数} {c : 整数} (hs : 对任意 x in s, c <= x)
  证明: by
  set r := Ico c (c + #s)
  calc
    _ <= ∑ x in r inter s, x + #(r \ s) • (c + #s) := by
      grw [← sum_inter_add_sum_sdiff r s, ← sum_le_card_nsmul _ _ _ fun x mx => ?_]
      rw [mem_sdiff]; rw [mem_Ico] at mx; exact mx.1.2.le
    _ = ∑ x in s inter r, x + #(s \ r) • (c + #s) := by
      rw 

Depends on / 依赖: Int.card_Ico, Int.toNat_natCast, add_sub_cancel_left, card_Ico, card_nsmul_le_sum, card_sdiff_comm, inter_comm, mem_Ico, mem_sdiff, sum_inter_add_sum_sdiff, sum_le_card_nsmul, toNat_natCast
-/
lemma sum_Ico_le_sum {s : Finset Int} {c : Int} (hs : forall x in s, c <= x) :
    ∑ x in Ico c (c + #s), x <= ∑ x in s, x := by
  set r := Ico c (c + #s)
  calc
    _ <= ∑ x in r inter s, x + #(r \ s) • (c + #s) := by
      grw [← sum_inter_add_sum_sdiff r s, ← sum_le_card_nsmul _ _ _ fun x mx => ?_]
      rw [mem_sdiff]; rw [mem_Ico] at mx; exact mx.1.2.le
    _ = ∑ x in s inter r, x + #(s \ r) • (c + #s) := by
      rw [inter_comm]; rw [card_sdiff_comm]
      rw [Int.card_Ico]; rw [add_sub_cancel_left]; rw [Int.toNat_natCast]
    _ <= _ := by
      grw [← sum_inter_add_sum_sdiff s r, card_nsmul_le_sum _ _ _ fun x mx => ?_]
      grind

/--
lemma `sum_range_le_sum` / 引理 `sum_range_le_sum`

English:
lemma sum_range_le_sum
  given: {s : Finset Int} {c : Int} (hs : forall x in s, c <= x)
  proof: by
  convert! sum_Ico_le_sum hs
  refine sum_nbij (c + ·) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro x mx; rw [mem_Ico]; rw [mem_range] at mx; lia
  · intro x mx y my (h : c + x = c + y); lia
  · intro x mx; simp_rw [coe_range, Set.mem_image, Set.mem_Iio]
    rw [mem_coe]; rw [mem_Ico] at mx
    use (x - c

中文:
引理 sum_range_le_sum
  条件: {s : 有限集 整数} {c : 整数} (hs : 对任意 x in s, c <= x)
  证明: by
  convert! sum_Ico_le_sum hs
  refine sum_nbij (c + ·) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro x mx; rw [mem_Ico]; rw [mem_range] at mx; lia
  · intro x mx y my (h : c + x = c + y); lia
  · intro x mx; simp_rw [coe_range, Set.mem_image, Set.mem_Iio]
    rw [mem_coe]; rw [mem_Ico] at mx
    use (x - c

Depends on / 依赖: Set.mem_Iio, Set.mem_image, coe_range, convert, mem_Ico, mem_Iio, mem_coe, mem_image, mem_range, simp_rw, sum_Ico_le_sum, sum_nbij
-/
lemma sum_range_le_sum {s : Finset Int} {c : Int} (hs : forall x in s, c <= x) :
    ∑ n in range #s, (c + n) <= ∑ x in s, x := by
  convert! sum_Ico_le_sum hs
  refine sum_nbij (c + ·) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro x mx; rw [mem_Ico]; rw [mem_range] at mx; lia
  · intro x mx y my (h : c + x = c + y); lia
  · intro x mx; simp_rw [coe_range, Set.mem_image, Set.mem_Iio]
    rw [mem_coe]; rw [mem_Ico] at mx
    use (x - c).toNat; grind

end Finset
