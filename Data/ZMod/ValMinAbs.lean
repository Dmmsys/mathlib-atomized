/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Linarith

/-!
# Absolute value in `ZMod n`
-/

@[expose] public section

namespace ZMod
variable {n : Nat} {a b : ZMod n}

/--
Definition of `valMinAbs` / `valMinAbs` 的定义

English:
definition valMinAbs
  signature: : forall {n : Nat}, ZMod n -> Int

中文:
定义 valMinAbs
  签名: : 对任意 {n : 自然数}, ZMod n -> 整数
-/
def valMinAbs : forall {n : Nat}, ZMod n -> Int
  | 0, x => x
  | n@(_ + 1), x => if x.val <= n / 2 then x.val else (x.val : Int) - n

/--
lemma `valMinAbs_def_zero` / 引理 `valMinAbs_def_zero`

English:
lemma valMinAbs_def_zero
  given: (x : ZMod 0)
  statement: valMinAbs x = x
  proof: rfl

中文:
引理 valMinAbs_def_zero
  条件: (x : ZMod 0)
  结论: valMinAbs x = x
  证明: rfl
-/
@[simp] lemma valMinAbs_def_zero (x : ZMod 0) : valMinAbs x = x := rfl

/--
lemma `valMinAbs_def_pos` / 引理 `valMinAbs_def_pos`

English:
lemma valMinAbs_def_pos
  statement: forall {n : Nat} [NeZero n] (x : ZMod n),

中文:
引理 valMinAbs_def_pos
  结论: 对任意 {n : 自然数} [NeZero n] (x : ZMod n),
-/
lemma valMinAbs_def_pos : forall {n : Nat} [NeZero n] (x : ZMod n),
    valMinAbs x = if x.val <= n / 2 then (x.val : Int) else x.val - n
  | 0, _, x => by cases NeZero.ne 0 rfl
  | n + 1, _, x => rfl

@[simp, norm_cast]
/--
lemma `coe_valMinAbs` / 引理 `coe_valMinAbs`

English:
lemma coe_valMinAbs
  statement: forall {n : Nat} (x : ZMod n), (x.valMinAbs : ZMod n) = x

中文:
引理 coe_valMinAbs
  结论: 对任意 {n : 自然数} (x : ZMod n), (x.valMinAbs : ZMod n) = x
-/
lemma coe_valMinAbs : forall {n : Nat} (x : ZMod n), (x.valMinAbs : ZMod n) = x
  | 0, _ => Int.cast_id
  | k@(n + 1), x => by
    rw [valMinAbs_def_pos]
    split_ifs
    · rw [Int.cast_natCast, natCast_zmod_val]
    · rw [Int.cast_sub, Int.cast_natCast, natCast_zmod_val, Int.cast_natCast, natCast_self,
        sub_zero]

/--
lemma `injective_valMinAbs` / 引理 `injective_valMinAbs`

English:
lemma injective_valMinAbs
  statement: (valMinAbs : ZMod n -> Int).Injective
  proof: Function.injective_iff_hasLeftInverse.2 ⟨_, coe_valMinAbs⟩

@[simp]

中文:
引理 injective_valMinAbs
  结论: (valMinAbs : ZMod n -> 整数).Injective
  证明: Function.injective_iff_hasLeftInverse.2 ⟨_, coe_valMinAbs⟩

@[simp]

Depends on / 依赖: Function, Function.injective_iff_hasLeftInverse, coe_valMinAbs, injective_iff_hasLeftInverse
-/
lemma injective_valMinAbs : (valMinAbs : ZMod n -> Int).Injective :=
  Function.injective_iff_hasLeftInverse.2 ⟨_, coe_valMinAbs⟩

@[simp]
/--
theorem `valMinAbs_inj` / 定理 `valMinAbs_inj`

English:
theorem valMinAbs_inj
  statement: a.valMinAbs = b.valMinAbs ↔ a = b
  proof: ZMod.injective_valMinAbs.eq_iff

中文:
定理 valMinAbs_inj
  结论: a.valMinAbs = b.valMinAbs ↔ a = b
  证明: ZMod.injective_valMinAbs.eq_iff

Depends on / 依赖: ZMod.injective_valMinAbs.eq_iff, eq_iff, injective_valMinAbs
-/
theorem valMinAbs_inj : a.valMinAbs = b.valMinAbs ↔ a = b :=
  ZMod.injective_valMinAbs.eq_iff

/--
lemma `valMinAbs_nonneg_iff` / 引理 `valMinAbs_nonneg_iff`

English:
lemma valMinAbs_nonneg_iff
  given: [NeZero n] (x : ZMod n)
  statement: 0 <= x.valMinAbs ↔ x.val <= n / 2
  proof: by
  rw [valMinAbs_def_pos]; split_ifs with h
  · exact iff_of_true (Nat.cast_nonneg _) h
  · exact iff_of_false (sub_lt_zero.2 <| Int.ofNat_lt.2 x.val_lt).not_ge h

中文:
引理 valMinAbs_nonneg_iff
  条件: [NeZero n] (x : ZMod n)
  结论: 0 <= x.valMinAbs ↔ x.val <= n / 2
  证明: by
  rw [valMinAbs_def_pos]; split_ifs with h
  · exact iff_of_true (Nat.cast_nonneg _) h
  · exact iff_of_false (sub_lt_zero.2 <| Int.ofNat_lt.2 x.val_lt).not_ge h

Depends on / 依赖: Int.ofNat_lt, Nat.cast_nonneg, cast_nonneg, iff_of_false, iff_of_true, not_ge, ofNat_lt, split_ifs, sub_lt_zero, valMinAbs_def_pos, val_lt, x.val_lt
-/
lemma valMinAbs_nonneg_iff [NeZero n] (x : ZMod n) : 0 <= x.valMinAbs ↔ x.val <= n / 2 := by
  rw [valMinAbs_def_pos]; split_ifs with h
  · exact iff_of_true (Nat.cast_nonneg _) h
  · exact iff_of_false (sub_lt_zero.2 <| Int.ofNat_lt.2 x.val_lt).not_ge h

set_option backward.isDefEq.respectTransparency false in
/--
lemma `valMinAbs_mul_two_eq_iff` / 引理 `valMinAbs_mul_two_eq_iff`

English:
lemma valMinAbs_mul_two_eq_iff
  given: (a : ZMod n)
  statement: a.valMinAbs * 2 = n ↔ 2 * a.val = n
  proof: by
  rcases n with - | n
  · simp
  by_cases h : a.val <= n.succ / 2
  · dsimp [valMinAbs]
    rw [if_pos h]; rw [← Int.natCast_inj]; rw [Nat.cast_mul]; rw [Nat.cast_two]; rw [mul_comm]; rw [Int.natCast_add]; rw [Nat.cast_one]
  apply iff_of_false _ (mt _ h)
  · intro he
    rw [← a.valMinAbs_nonneg

中文:
引理 valMinAbs_mul_two_eq_iff
  条件: (a : ZMod n)
  结论: a.valMinAbs * 2 = n ↔ 2 * a.val = n
  证明: by
  rcases n with - | n
  · simp
  by_cases h : a.val <= n.succ / 2
  · dsimp [valMinAbs]
    rw [if_pos h]; rw [← Int.natCast_inj]; rw [Nat.cast_mul]; rw [Nat.cast_two]; rw [mul_comm]; rw [Int.natCast_add]; rw [Nat.cast_one]
  apply iff_of_false _ (mt _ h)
  · intro he
    rw [← a.valMinAbs_nonneg

Depends on / 依赖: Int.natCast_add, Int.natCast_inj, Nat.cast_mul, Nat.cast_nonneg, Nat.cast_one, Nat.cast_two, Nat.le_div_iff_mul_le, a.val, a.valMinAbs_nonneg_iff, cast_mul, cast_nonneg, cast_one, cast_two, exacts, h.le, if_pos, iff_of_false, le_div_iff_mul_le, mul_comm, mul_nonneg_iff_left_nonneg_of_pos
-/
lemma valMinAbs_mul_two_eq_iff (a : ZMod n) : a.valMinAbs * 2 = n ↔ 2 * a.val = n := by
  rcases n with - | n
  · simp
  by_cases h : a.val <= n.succ / 2
  · dsimp [valMinAbs]
    rw [if_pos h]; rw [← Int.natCast_inj]; rw [Nat.cast_mul]; rw [Nat.cast_two]; rw [mul_comm]; rw [Int.natCast_add]; rw [Nat.cast_one]
  apply iff_of_false _ (mt _ h)
  · intro he
    rw [← a.valMinAbs_nonneg_iff]; rw [← mul_nonneg_iff_left_nonneg_of_pos]; rw [he] at h
    exacts [h (Nat.cast_nonneg _), zero_lt_two]
  · rw [mul_comm]
    exact fun h => (Nat.le_div_iff_mul_le zero_lt_two).2 h.le

/--
lemma `valMinAbs_mem_Ioc` / 引理 `valMinAbs_mem_Ioc`

English:
lemma valMinAbs_mem_Ioc
  given: [NeZero n] (x : ZMod n)
  statement: x.valMinAbs * 2 in Set.Ioc (-n : Int) n
  proof: by
  simp_rw [valMinAbs_def_pos, Nat.le_div_two_iff_mul_two_le]; split_ifs with h
  · exact ⟨(neg_lt_zero.2 <| mod_cast NeZero.pos n).trans_le (by positivity), h⟩
· refine ⟨?_, le_trans (mul_nonpos_of_nonpos_of_nonneg ?_ zero_le_two) Nat.cast_nonneg _⟩
    · linarith only [h]
    · grind

中文:
引理 valMinAbs_mem_Ioc
  条件: [NeZero n] (x : ZMod n)
  结论: x.valMinAbs * 2 in Set.Ioc (-n : 整数) n
  证明: by
  simp_rw [valMinAbs_def_pos, Nat.le_div_two_iff_mul_two_le]; split_ifs with h
  · exact ⟨(neg_lt_zero.2 <| mod_cast NeZero.pos n).trans_le (by positivity), h⟩
· refine ⟨?_, le_trans (mul_nonpos_of_nonpos_of_nonneg ?_ zero_le_two) Nat.cast_nonneg _⟩
    · linarith only [h]
    · grind

Depends on / 依赖: Nat.cast_nonneg, Nat.le_div_two_iff_mul_two_le, NeZero, NeZero.pos, cast_nonneg, le_div_two_iff_mul_two_le, le_trans, mod_cast, mul_nonpos_of_nonpos_of_nonneg, neg_lt_zero, simp_rw, split_ifs, trans_le, valMinAbs_def_pos, zero_le_two
-/
lemma valMinAbs_mem_Ioc [NeZero n] (x : ZMod n) : x.valMinAbs * 2 in Set.Ioc (-n : Int) n := by
  simp_rw [valMinAbs_def_pos, Nat.le_div_two_iff_mul_two_le]; split_ifs with h
  · exact ⟨(neg_lt_zero.2 <| mod_cast NeZero.pos n).trans_le (by positivity), h⟩
· refine ⟨?_, le_trans (mul_nonpos_of_nonpos_of_nonneg ?_ zero_le_two) Nat.cast_nonneg _⟩
    · linarith only [h]
    · grind

/--
lemma `valMinAbs_spec` / 引理 `valMinAbs_spec`

English:
lemma valMinAbs_spec
  given: [NeZero n] (x : ZMod n) (y : Int)
  proof: by rintro rfl; exact ⟨x.coe_valMinAbs.symm, x.valMinAbs_mem_Ioc⟩
  mpr h := by
    rw [← sub_eq_zero]
    apply @Int.eq_zero_of_abs_lt_dvd n
    · rw [← intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, coe_valMinAbs, h.1, sub_self]
    rw [← mul_lt_mul_iff_left₀ (@zero_lt_two Int _ _ _ _ _)]
    nth_rw 1

中文:
引理 valMinAbs_spec
  条件: [NeZero n] (x : ZMod n) (y : 整数)
  证明: by rintro rfl; exact ⟨x.coe_valMinAbs.symm, x.valMinAbs_mem_Ioc⟩
  mpr h := by
    rw [← sub_eq_zero]
    apply @Int.eq_zero_of_abs_lt_dvd n
    · rw [← intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, coe_valMinAbs, h.1, sub_self]
    rw [← mul_lt_mul_iff_left₀ (@zero_lt_two Int _ _ _ _ _)]
    nth_rw 1

Depends on / 依赖: Int.cast_sub, Int.eq_zero_of_abs_lt_dvd, abs_eq_self, abs_lt, abs_mul, cast_sub, coe_valMinAbs, eq_zero_of_abs_lt_dvd, intCast_zmod_eq_zero_iff_dvd, nth_rw, sub_eq_zero, sub_mul, sub_self, valMinAbs_mem_Ioc, x.coe_valMinAbs.symm, x.valMinAbs_mem_Ioc, zero_le_two, zero_lt_two
-/
lemma valMinAbs_spec [NeZero n] (x : ZMod n) (y : Int) :
    x.valMinAbs = y ↔ x = y ∧ y * 2 in Set.Ioc (-n : Int) n where
  mp := by rintro rfl; exact ⟨x.coe_valMinAbs.symm, x.valMinAbs_mem_Ioc⟩
  mpr h := by
    rw [← sub_eq_zero]
    apply @Int.eq_zero_of_abs_lt_dvd n
    · rw [← intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, coe_valMinAbs, h.1, sub_self]
    rw [← mul_lt_mul_iff_left₀ (@zero_lt_two Int _ _ _ _ _)]
    nth_rw 1 [← abs_eq_self.2 (@zero_le_two Int _ _ _ _)]
    rw [← abs_mul]; rw [sub_mul]; rw [abs_lt]
    constructor <;> linarith only [x.valMinAbs_mem_Ioc.1, x.valMinAbs_mem_Ioc.2, h.2.1, h.2.2]

/--
lemma `natAbs_valMinAbs_le` / 引理 `natAbs_valMinAbs_le`

English:
lemma natAbs_valMinAbs_le
  given: [NeZero n] (x : ZMod n)
  statement: x.valMinAbs.natAbs <= n / 2
  proof: by
  rw [Nat.le_div_two_iff_mul_two_le]
  rcases x.valMinAbs.natAbs_eq with h | h
  · rw [← h]
    exact x.valMinAbs_mem_Ioc.2
  · rw [← neg_le_neg_iff, ← neg_mul, ← h]
    exact x.valMinAbs_mem_Ioc.1.le

中文:
引理 natAbs_valMinAbs_le
  条件: [NeZero n] (x : ZMod n)
  结论: x.valMinAbs.natAbs <= n / 2
  证明: by
  rw [Nat.le_div_two_iff_mul_two_le]
  rcases x.valMinAbs.natAbs_eq with h | h
  · rw [← h]
    exact x.valMinAbs_mem_Ioc.2
  · rw [← neg_le_neg_iff, ← neg_mul, ← h]
    exact x.valMinAbs_mem_Ioc.1.le

Depends on / 依赖: Nat.le_div_two_iff_mul_two_le, le_div_two_iff_mul_two_le, natAbs_eq, neg_le_neg_iff, neg_mul, valMinAbs, valMinAbs_mem_Ioc, x.valMinAbs.natAbs_eq, x.valMinAbs_mem_Ioc
-/
lemma natAbs_valMinAbs_le [NeZero n] (x : ZMod n) : x.valMinAbs.natAbs <= n / 2 := by
  rw [Nat.le_div_two_iff_mul_two_le]
  rcases x.valMinAbs.natAbs_eq with h | h
  · rw [← h]
    exact x.valMinAbs_mem_Ioc.2
  · rw [← neg_le_neg_iff, ← neg_mul, ← h]
    exact x.valMinAbs_mem_Ioc.1.le

set_option backward.isDefEq.respectTransparency false in
/--
theorem `eq_neg_of_valMinAbs_eq_neg_valMinAbs` / 定理 `eq_neg_of_valMinAbs_eq_neg_valMinAbs`

English:
theorem eq_neg_of_valMinAbs_eq_neg_valMinAbs
  given: (h : a.valMinAbs = -b.valMinAbs)
  statement: a = -b
  proof: by
  rcases eq_zero_or_neZero n with rfl | hn <;> simp_all [valMinAbs_spec]

中文:
定理 eq_neg_of_valMinAbs_eq_neg_valMinAbs
  条件: (h : a.valMinAbs = -b.valMinAbs)
  结论: a = -b
  证明: by
  rcases eq_zero_or_neZero n with rfl | hn <;> simp_all [valMinAbs_spec]

Depends on / 依赖: eq_zero_or_neZero, valMinAbs_spec
-/
theorem eq_neg_of_valMinAbs_eq_neg_valMinAbs (h : a.valMinAbs = -b.valMinAbs) : a = -b := by
  rcases eq_zero_or_neZero n with rfl | hn <;> simp_all [valMinAbs_spec]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `valMinAbs_zero` / 引理 `valMinAbs_zero`

English:
lemma valMinAbs_zero
  statement: forall n, (0 : ZMod n).valMinAbs = 0

中文:
引理 valMinAbs_zero
  结论: 对任意 n, (0 : ZMod n).valMinAbs = 0
-/
lemma valMinAbs_zero : forall n, (0 : ZMod n).valMinAbs = 0
  | 0 => by simp only [valMinAbs_def_zero]
  | n + 1 => by simp only [valMinAbs_def_pos, if_true, Int.ofNat_zero, zero_le, val_zero]

@[simp]
/--
lemma `valMinAbs_eq_zero` / 引理 `valMinAbs_eq_zero`

English:
lemma valMinAbs_eq_zero
  given: (x : ZMod n)
  statement: x.valMinAbs = 0 ↔ x = 0
  proof: injective_valMinAbs.eq_iff' valMinAbs_zero _

中文:
引理 valMinAbs_eq_zero
  条件: (x : ZMod n)
  结论: x.valMinAbs = 0 ↔ x = 0
  证明: injective_valMinAbs.eq_iff' valMinAbs_zero _

Depends on / 依赖: eq_iff, injective_valMinAbs, injective_valMinAbs.eq_iff, valMinAbs_zero
-/
lemma valMinAbs_eq_zero (x : ZMod n) : x.valMinAbs = 0 ↔ x = 0 :=
injective_valMinAbs.eq_iff' valMinAbs_zero _

/--
lemma `natCast_natAbs_valMinAbs` / 引理 `natCast_natAbs_valMinAbs`

English:
lemma natCast_natAbs_valMinAbs
  given: [NeZero n] (a : ZMod n)
  proof: by
  have : (a.val : Int) - n <= 0 := by
    rw [sub_nonpos]; rw [Int.ofNat_le]
    exact a.val_le
  rw [valMinAbs_def_pos]
  split_ifs
  · rw [Int.natAbs_natCast, natCast_zmod_val]
  · rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos this, Int.cast_neg, Int.cast_sub,
      Int.cast_natCast, Int.c

中文:
引理 natCast_natAbs_valMinAbs
  条件: [NeZero n] (a : ZMod n)
  证明: by
  have : (a.val : Int) - n <= 0 := by
    rw [sub_nonpos]; rw [Int.ofNat_le]
    exact a.val_le
  rw [valMinAbs_def_pos]
  split_ifs
  · rw [Int.natAbs_natCast, natCast_zmod_val]
  · rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos this, Int.cast_neg, Int.cast_sub,
      Int.cast_natCast, Int.c

Depends on / 依赖: Int.cast_natCast, Int.cast_neg, Int.cast_sub, Int.natAbs_natCast, Int.ofNat_le, Int.ofNat_natAbs_of_nonpos, a.val, a.val_le, cast_natCast, cast_neg, cast_sub, natAbs_natCast, natCast_self, natCast_zmod_val, ofNat_le, ofNat_natAbs_of_nonpos, split_ifs, sub_nonpos, sub_zero, valMinAbs_def_pos
-/
lemma natCast_natAbs_valMinAbs [NeZero n] (a : ZMod n) :
    (a.valMinAbs.natAbs : ZMod n) = if a.val <= (n : Nat) / 2 then a else -a := by
  have : (a.val : Int) - n <= 0 := by
    rw [sub_nonpos]; rw [Int.ofNat_le]
    exact a.val_le
  rw [valMinAbs_def_pos]
  split_ifs
  · rw [Int.natAbs_natCast, natCast_zmod_val]
  · rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos this, Int.cast_neg, Int.cast_sub,
      Int.cast_natCast, Int.cast_natCast, natCast_self, sub_zero, natCast_zmod_val]

/--
lemma `valMinAbs_neg_of_ne_half` / 引理 `valMinAbs_neg_of_ne_half`

English:
lemma valMinAbs_neg_of_ne_half
  given: (ha : 2 * a.val != n)
  statement: (-a).valMinAbs = -a.valMinAbs
  proof: by
  rcases eq_zero_or_neZero n with rfl | h
  · rfl
  refine (valMinAbs_spec _ _).2 ⟨?_, ?_, ?_⟩
  · rw [Int.cast_neg, coe_valMinAbs]
  · rw [neg_mul, neg_lt_neg_iff]
    exact a.valMinAbs_mem_Ioc.2.lt_of_ne (mt a.valMinAbs_mul_two_eq_iff.1 ha)
  · linarith only [a.valMinAbs_mem_Ioc.1]

@[simp]

中文:
引理 valMinAbs_neg_of_ne_half
  条件: (ha : 2 * a.val != n)
  结论: (-a).valMinAbs = -a.valMinAbs
  证明: by
  rcases eq_zero_or_neZero n with rfl | h
  · rfl
  refine (valMinAbs_spec _ _).2 ⟨?_, ?_, ?_⟩
  · rw [Int.cast_neg, coe_valMinAbs]
  · rw [neg_mul, neg_lt_neg_iff]
    exact a.valMinAbs_mem_Ioc.2.lt_of_ne (mt a.valMinAbs_mul_two_eq_iff.1 ha)
  · linarith only [a.valMinAbs_mem_Ioc.1]

@[simp]

Depends on / 依赖: Int.cast_neg, a.valMinAbs_mem_Ioc, a.valMinAbs_mul_two_eq_iff, cast_neg, coe_valMinAbs, eq_zero_or_neZero, lt_of_ne, neg_lt_neg_iff, neg_mul, valMinAbs_mem_Ioc, valMinAbs_mul_two_eq_iff, valMinAbs_spec
-/
lemma valMinAbs_neg_of_ne_half (ha : 2 * a.val != n) : (-a).valMinAbs = -a.valMinAbs := by
  rcases eq_zero_or_neZero n with rfl | h
  · rfl
  refine (valMinAbs_spec _ _).2 ⟨?_, ?_, ?_⟩
  · rw [Int.cast_neg, coe_valMinAbs]
  · rw [neg_mul, neg_lt_neg_iff]
    exact a.valMinAbs_mem_Ioc.2.lt_of_ne (mt a.valMinAbs_mul_two_eq_iff.1 ha)
  · linarith only [a.valMinAbs_mem_Ioc.1]

@[simp]
/--
lemma `natAbs_valMinAbs_neg` / 引理 `natAbs_valMinAbs_neg`

English:
lemma natAbs_valMinAbs_neg
  given: (a : ZMod n)
  statement: (-a).valMinAbs.natAbs = a.valMinAbs.natAbs
  proof: by
  by_cases h2a : 2 * a.val = n
  · rw [a.neg_eq_self_iff.2 (Or.inr h2a)]
  · rw [valMinAbs_neg_of_ne_half h2a, Int.natAbs_neg]

中文:
引理 natAbs_valMinAbs_neg
  条件: (a : ZMod n)
  结论: (-a).valMinAbs.natAbs = a.valMinAbs.natAbs
  证明: by
  by_cases h2a : 2 * a.val = n
  · rw [a.neg_eq_self_iff.2 (Or.inr h2a)]
  · rw [valMinAbs_neg_of_ne_half h2a, Int.natAbs_neg]

Depends on / 依赖: Int.natAbs_neg, Or.inr, a.neg_eq_self_iff, a.val, natAbs_neg, neg_eq_self_iff, valMinAbs_neg_of_ne_half
-/
lemma natAbs_valMinAbs_neg (a : ZMod n) : (-a).valMinAbs.natAbs = a.valMinAbs.natAbs := by
  by_cases h2a : 2 * a.val = n
  · rw [a.neg_eq_self_iff.2 (Or.inr h2a)]
  · rw [valMinAbs_neg_of_ne_half h2a, Int.natAbs_neg]

/--
theorem `natAbs_valMinAbs_eq_natAbs_valMinAbs` / 定理 `natAbs_valMinAbs_eq_natAbs_valMinAbs`

English:
theorem natAbs_valMinAbs_eq_natAbs_valMinAbs
  proof: by
  constructor
  · rw [Int.natAbs_eq_natAbs_iff, valMinAbs_inj]
    exact Or.imp_right eq_neg_of_valMinAbs_eq_neg_valMinAbs
  · rintro (rfl | rfl)
    · rfl
    · rw [natAbs_valMinAbs_neg]

中文:
定理 natAbs_valMinAbs_eq_natAbs_valMinAbs
  证明: by
  constructor
  · rw [Int.natAbs_eq_natAbs_iff, valMinAbs_inj]
    exact Or.imp_right eq_neg_of_valMinAbs_eq_neg_valMinAbs
  · rintro (rfl | rfl)
    · rfl
    · rw [natAbs_valMinAbs_neg]

Depends on / 依赖: Int.natAbs_eq_natAbs_iff, Or.imp_right, eq_neg_of_valMinAbs_eq_neg_valMinAbs, imp_right, natAbs_eq_natAbs_iff, natAbs_valMinAbs_neg, valMinAbs_inj
-/
theorem natAbs_valMinAbs_eq_natAbs_valMinAbs :
    a.valMinAbs.natAbs = b.valMinAbs.natAbs ↔ a = b ∨ a = -b := by
  constructor
  · rw [Int.natAbs_eq_natAbs_iff, valMinAbs_inj]
    exact Or.imp_right eq_neg_of_valMinAbs_eq_neg_valMinAbs
  · rintro (rfl | rfl)
    · rfl
    · rw [natAbs_valMinAbs_neg]

/--
theorem `abs_valMinAbs_eq_abs_valMinAbs` / 定理 `abs_valMinAbs_eq_abs_valMinAbs`

English:
theorem abs_valMinAbs_eq_abs_valMinAbs
  proof: by
  rw [← natAbs_valMinAbs_eq_natAbs_valMinAbs]; rw [Int.abs_eq_natAbs]; rw [Int.abs_eq_natAbs]
  norm_cast

中文:
定理 abs_valMinAbs_eq_abs_valMinAbs
  证明: by
  rw [← natAbs_valMinAbs_eq_natAbs_valMinAbs]; rw [Int.abs_eq_natAbs]; rw [Int.abs_eq_natAbs]
  norm_cast

Depends on / 依赖: Int.abs_eq_natAbs, abs_eq_natAbs, natAbs_valMinAbs_eq_natAbs_valMinAbs
-/
theorem abs_valMinAbs_eq_abs_valMinAbs :
    |a.valMinAbs| = |b.valMinAbs| ↔ a = b ∨ a = -b := by
  rw [← natAbs_valMinAbs_eq_natAbs_valMinAbs]; rw [Int.abs_eq_natAbs]; rw [Int.abs_eq_natAbs]
  norm_cast

/--
lemma `val_eq_ite_valMinAbs` / 引理 `val_eq_ite_valMinAbs`

English:
lemma val_eq_ite_valMinAbs
  given: [NeZero n] (a : ZMod n)
  proof: by
  rw [valMinAbs_def_pos]
  split_ifs <;> simp [add_zero, sub_add_cancel]

中文:
引理 val_eq_ite_valMinAbs
  条件: [NeZero n] (a : ZMod n)
  证明: by
  rw [valMinAbs_def_pos]
  split_ifs <;> simp [add_zero, sub_add_cancel]

Depends on / 依赖: add_zero, split_ifs, sub_add_cancel, valMinAbs_def_pos
-/
lemma val_eq_ite_valMinAbs [NeZero n] (a : ZMod n) :
    (a.val : Int) = a.valMinAbs + if a.val <= n / 2 then 0 else n := by
  rw [valMinAbs_def_pos]
  split_ifs <;> simp [add_zero, sub_add_cancel]

/--
lemma `prime_ne_zero` / 引理 `prime_ne_zero`

English:
lemma prime_ne_zero
  given: (p q : Nat) [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p != q)
  proof: by
  rwa [← Nat.cast_zero, Ne, natCast_eq_natCast_iff, Nat.modEq_zero_iff_dvd,
    ← hp.1.coprime_iff_not_dvd, Nat.coprime_primes hp.1 hq.1]

中文:
引理 prime_ne_zero
  条件: (p q : 自然数) [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p != q)
  证明: by
  rwa [← Nat.cast_zero, Ne, natCast_eq_natCast_iff, Nat.modEq_zero_iff_dvd,
    ← hp.1.coprime_iff_not_dvd, Nat.coprime_primes hp.1 hq.1]

Depends on / 依赖: Nat.cast_zero, Nat.coprime_primes, Nat.modEq_zero_iff_dvd, cast_zero, coprime_iff_not_dvd, coprime_primes, modEq_zero_iff_dvd, natCast_eq_natCast_iff
-/
lemma prime_ne_zero (p q : Nat) [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p != q) :
    (q : ZMod p) != 0 := by
  rwa [← Nat.cast_zero, Ne, natCast_eq_natCast_iff, Nat.modEq_zero_iff_dvd,
    ← hp.1.coprime_iff_not_dvd, Nat.coprime_primes hp.1 hq.1]

variable {n a : Nat}

/--
lemma `valMinAbs_natAbs_eq_min` / 引理 `valMinAbs_natAbs_eq_min`

English:
lemma valMinAbs_natAbs_eq_min
  given: [hpos : NeZero n] (a : ZMod n)
  proof: by
  rw [valMinAbs_def_pos]
  have := a.val_lt
  omega

中文:
引理 valMinAbs_natAbs_eq_min
  条件: [hpos : NeZero n] (a : ZMod n)
  证明: by
  rw [valMinAbs_def_pos]
  have := a.val_lt
  omega

Depends on / 依赖: a.val_lt, valMinAbs_def_pos, val_lt
-/
lemma valMinAbs_natAbs_eq_min [hpos : NeZero n] (a : ZMod n) :
    a.valMinAbs.natAbs = min a.val (n - a.val) := by
  rw [valMinAbs_def_pos]
  have := a.val_lt
  omega

set_option backward.isDefEq.respectTransparency false in
/--
lemma `valMinAbs_natCast_of_le_half` / 引理 `valMinAbs_natCast_of_le_half`

English:
lemma valMinAbs_natCast_of_le_half
  given: (ha : a <= n / 2)
  statement: (a : ZMod n).valMinAbs = a
  proof: by
  cases n
  · simp
  · simp [valMinAbs_def_pos, val_natCast, Nat.mod_eq_of_lt (ha.trans_lt <| Nat.div_lt_self' _ 0),
      ha]

中文:
引理 valMinAbs_natCast_of_le_half
  条件: (ha : a <= n / 2)
  结论: (a : ZMod n).valMinAbs = a
  证明: by
  cases n
  · simp
  · simp [valMinAbs_def_pos, val_natCast, Nat.mod_eq_of_lt (ha.trans_lt <| Nat.div_lt_self' _ 0),
      ha]

Depends on / 依赖: Nat.div_lt_self, Nat.mod_eq_of_lt, div_lt_self, ha.trans_lt, mod_eq_of_lt, trans_lt, valMinAbs_def_pos, val_natCast
-/
lemma valMinAbs_natCast_of_le_half (ha : a <= n / 2) : (a : ZMod n).valMinAbs = a := by
  cases n
  · simp
  · simp [valMinAbs_def_pos, val_natCast, Nat.mod_eq_of_lt (ha.trans_lt <| Nat.div_lt_self' _ 0),
      ha]

/--
lemma `valMinAbs_natCast_of_half_lt` / 引理 `valMinAbs_natCast_of_half_lt`

English:
lemma valMinAbs_natCast_of_half_lt
  given: (ha : n / 2 < a) (ha' : a < n)
  proof: by
  cases n
  · cases not_lt_bot ha'
  · simp [valMinAbs_def_pos, val_natCast, Nat.mod_eq_of_lt ha', ha.not_ge]

@[simp]

中文:
引理 valMinAbs_natCast_of_half_lt
  条件: (ha : n / 2 < a) (ha' : a < n)
  证明: by
  cases n
  · cases not_lt_bot ha'
  · simp [valMinAbs_def_pos, val_natCast, Nat.mod_eq_of_lt ha', ha.not_ge]

@[simp]

Depends on / 依赖: Nat.mod_eq_of_lt, ha.not_ge, mod_eq_of_lt, not_ge, not_lt_bot, valMinAbs_def_pos, val_natCast
-/
lemma valMinAbs_natCast_of_half_lt (ha : n / 2 < a) (ha' : a < n) :
    (a : ZMod n).valMinAbs = a - n := by
  cases n
  · cases not_lt_bot ha'
  · simp [valMinAbs_def_pos, val_natCast, Nat.mod_eq_of_lt ha', ha.not_ge]

@[simp]
/--
lemma `valMinAbs_natCast_eq_self` / 引理 `valMinAbs_natCast_eq_self`

English:
lemma valMinAbs_natCast_eq_self
  given: [NeZero n]
  statement: (a : ZMod n).valMinAbs = a ↔ a <= n / 2
  proof: by
  refine ⟨fun ha => ?_, valMinAbs_natCast_of_le_half⟩
  rw [← Int.natAbs_natCast a]; rw [← ha]
  exact natAbs_valMinAbs_le (n := n) a

中文:
引理 valMinAbs_natCast_eq_self
  条件: [NeZero n]
  结论: (a : ZMod n).valMinAbs = a ↔ a <= n / 2
  证明: by
  refine ⟨fun ha => ?_, valMinAbs_natCast_of_le_half⟩
  rw [← Int.natAbs_natCast a]; rw [← ha]
  exact natAbs_valMinAbs_le (n := n) a

Depends on / 依赖: Int.natAbs_natCast, natAbs_natCast, natAbs_valMinAbs_le, valMinAbs_natCast_of_le_half
-/
lemma valMinAbs_natCast_eq_self [NeZero n] : (a : ZMod n).valMinAbs = a ↔ a <= n / 2 := by
  refine ⟨fun ha => ?_, valMinAbs_natCast_of_le_half⟩
  rw [← Int.natAbs_natCast a]; rw [← ha]
  exact natAbs_valMinAbs_le (n := n) a

/--
lemma `natAbs_valMinAbs_add_le` / 引理 `natAbs_valMinAbs_add_le`

English:
lemma natAbs_valMinAbs_add_le
  given: (a b : ZMod n)
  proof: by
  rcases n with - | n
  · rfl
  apply natAbs_min_of_le_div_two n.succ
  · simp_rw [Int.cast_add, coe_valMinAbs]
  · apply natAbs_valMinAbs_le

中文:
引理 natAbs_valMinAbs_add_le
  条件: (a b : ZMod n)
  证明: by
  rcases n with - | n
  · rfl
  apply natAbs_min_of_le_div_two n.succ
  · simp_rw [Int.cast_add, coe_valMinAbs]
  · apply natAbs_valMinAbs_le

Depends on / 依赖: Int.cast_add, cast_add, coe_valMinAbs, n.succ, natAbs_min_of_le_div_two, natAbs_valMinAbs_le, simp_rw
-/
lemma natAbs_valMinAbs_add_le (a b : ZMod n) :
    (a + b).valMinAbs.natAbs <= (a.valMinAbs + b.valMinAbs).natAbs := by
  rcases n with - | n
  · rfl
  apply natAbs_min_of_le_div_two n.succ
  · simp_rw [Int.cast_add, coe_valMinAbs]
  · apply natAbs_valMinAbs_le

end ZMod
