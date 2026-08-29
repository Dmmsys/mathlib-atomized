/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Data.List.MinMax
public import Mathlib.Data.Multiset.Fold

/-!
# Big operators on a multiset in ordered groups

This file contains the results concerning the interaction of multiset big operators with ordered
groups.
-/

public section

assert_not_exists MonoidWithZero

variable {ι α β : Type*}

namespace Multiset
section OrderedCommMonoid
variable [CommMonoid α] [Preorder α] {s t : Multiset α} {a : α}

@[to_additive sum_nonneg]
/--
lemma `one_le_prod_of_one_le` / 引理 `one_le_prod_of_one_le`

English:
lemma one_le_prod_of_one_le
  given: [MulLeftMono α]
  statement: (forall x in s, (1 : α) <= x) -> 1 <= s.prod
  proof: Quotient.inductionOn s fun l hl => by simpa using List.one_le_prod_of_one_le hl

@[to_additive]

中文:
引理 one_le_prod_of_one_le
  条件: [MulLeftMono α]
  结论: (对任意 x in s, (1 : α) <= x) -> 1 <= s.乘积
  证明: Quotient.inductionOn s fun l hl => by simpa using List.one_le_prod_of_one_le hl

@[to_additive]

Depends on / 依赖: List.one_le_prod_of_one_le, Quotient, Quotient.inductionOn, inductionOn, one_le_prod_of_one_le
-/
lemma one_le_prod_of_one_le [MulLeftMono α] : (forall x in s, (1 : α) <= x) -> 1 <= s.prod :=
  Quotient.inductionOn s fun l hl => by simpa using List.one_le_prod_of_one_le hl

@[to_additive]
/--
lemma `single_le_prod` / 引理 `single_le_prod`

English:
lemma single_le_prod
  given: [IsOrderedMonoid α]
  statement: (forall x in s, (1 : α) <= x) -> forall x in s, x <= s.prod
  proof: Quotient.inductionOn s fun l hl x hx => by simpa using List.single_le_prod hl x hx

@[to_additive sum_le_card_nsmul]

中文:
引理 single_le_prod
  条件: [是Ordered幺半群 α]
  结论: (对任意 x in s, (1 : α) <= x) -> 对任意 x in s, x <= s.乘积
  证明: Quotient.inductionOn s fun l hl x hx => by simpa using List.single_le_prod hl x hx

@[to_additive sum_le_card_nsmul]

Depends on / 依赖: List.single_le_prod, Quotient, Quotient.inductionOn, inductionOn, single_le_prod
-/
lemma single_le_prod [IsOrderedMonoid α] : (forall x in s, (1 : α) <= x) -> forall x in s, x <= s.prod :=
  Quotient.inductionOn s fun l hl x hx => by simpa using List.single_le_prod hl x hx

@[to_additive sum_le_card_nsmul]
/--
lemma `prod_le_pow_card` / 引理 `prod_le_pow_card`

English:
lemma prod_le_pow_card
  given: [MulLeftMono α] (s : Multiset α) (n : α) (h : forall x in s, x <= n)
  proof: by
  induction s using Quotient.inductionOn
  simpa using List.prod_le_pow_card _ _ h

@[to_additive all_zero_of_le_zero_le_of_sum_eq_zero]

中文:
引理 prod_le_pow_card
  条件: [MulLeftMono α] (s : Multiset α) (n : α) (h : 对任意 x in s, x <= n)
  证明: by
  induction s using Quotient.inductionOn
  simpa using List.prod_le_pow_card _ _ h

@[to_additive all_zero_of_le_zero_le_of_sum_eq_zero]

Depends on / 依赖: List.prod_le_pow_card, Quotient, Quotient.inductionOn, inductionOn, prod_le_pow_card
-/
lemma prod_le_pow_card [MulLeftMono α] (s : Multiset α) (n : α) (h : forall x in s, x <= n) :
    s.prod <= n ^ card s := by
  induction s using Quotient.inductionOn
  simpa using List.prod_le_pow_card _ _ h

@[to_additive all_zero_of_le_zero_le_of_sum_eq_zero]
/--
lemma `all_one_of_le_one_le_of_prod_eq_one` / 引理 `all_one_of_le_one_le_of_prod_eq_one`

English:
lemma all_one_of_le_one_le_of_prod_eq_one
  statement: {α : Type*} [CommMonoid α]
  proof: Quotient.inductionOn s (by
    simp only [quot_mk_to_coe, prod_coe, mem_coe]
    exact fun l => List.all_one_of_le_one_le_of_prod_eq_one)

@[to_additive]

中文:
引理 all_one_of_le_one_le_of_prod_eq_one
  结论: {α : 类型} [交换幺半群 α]
  证明: Quotient.inductionOn s (by
    simp only [quot_mk_to_coe, prod_coe, mem_coe]
    exact fun l => List.all_one_of_le_one_le_of_prod_eq_one)

@[to_additive]

Depends on / 依赖: List.all_one_of_le_one_le_of_prod_eq_one, Quotient, Quotient.inductionOn, all_one_of_le_one_le_of_prod_eq_one, inductionOn, mem_coe, prod_coe, quot_mk_to_coe
-/
lemma all_one_of_le_one_le_of_prod_eq_one {α : Type*} [CommMonoid α]
  [PartialOrder α] [IsOrderedMonoid α] {s : Multiset α} :
    (forall x in s, (1 : α) <= x) -> s.prod = 1 -> forall x in s, x = (1 : α) :=
  Quotient.inductionOn s (by
    simp only [quot_mk_to_coe, prod_coe, mem_coe]
    exact fun l => List.all_one_of_le_one_le_of_prod_eq_one)

@[to_additive]
/--
lemma `prod_le_prod_of_rel_le` / 引理 `prod_le_prod_of_rel_le`

English:
lemma prod_le_prod_of_rel_le
  given: [MulLeftMono α] (h : s.Rel (· <= ·) t)
  statement: s.prod <= t.prod
  proof: by
  induction h with
  | zero => rfl
  | cons rh _ rt =>
    rw [prod_cons]; rw [prod_cons]
    exact mul_le_mul' rh rt

@[to_additive]

中文:
引理 prod_le_prod_of_rel_le
  条件: [MulLeftMono α] (h : s.关系 (· <= ·) t)
  结论: s.乘积 <= t.乘积
  证明: by
  induction h with
  | zero => rfl
  | cons rh _ rt =>
    rw [prod_cons]; rw [prod_cons]
    exact mul_le_mul' rh rt

@[to_additive]

Depends on / 依赖: mul_le_mul, prod_cons
-/
lemma prod_le_prod_of_rel_le [MulLeftMono α] (h : s.Rel (· <= ·) t) : s.prod <= t.prod := by
  induction h with
  | zero => rfl
  | cons rh _ rt =>
    rw [prod_cons]; rw [prod_cons]
    exact mul_le_mul' rh rt

@[to_additive]
/--
lemma `prod_map_le_prod_map` / 引理 `prod_map_le_prod_map`

English:
lemma prod_map_le_prod_map
  statement: [MulLeftMono α] {s : Multiset ι} (f : ι -> α) (g : ι -> α)
  proof: prod_le_prod_of_rel_le rel_map.2 rel_refl_of_refl_on h

@[to_additive]

中文:
引理 prod_map_le_prod_map
  结论: [MulLeftMono α] {s : Multiset ι} (f : ι -> α) (g : ι -> α)
  证明: prod_le_prod_of_rel_le rel_map.2 rel_refl_of_refl_on h

@[to_additive]

Depends on / 依赖: prod_le_prod_of_rel_le, rel_map, rel_refl_of_refl_on
-/
lemma prod_map_le_prod_map [MulLeftMono α] {s : Multiset ι} (f : ι -> α) (g : ι -> α)
    (h : forall i, i in s -> f i <= g i) : (s.map f).prod <= (s.map g).prod :=
prod_le_prod_of_rel_le rel_map.2 rel_refl_of_refl_on h

@[to_additive]
/--
lemma `prod_map_le_prod` / 引理 `prod_map_le_prod`

English:
lemma prod_map_le_prod
  given: [MulLeftMono α] (f : α -> α) (h : forall x, x in s -> f x <= x)
  proof: prod_le_prod_of_rel_le rel_map_left.2 rel_refl_of_refl_on h

@[to_additive]

中文:
引理 prod_map_le_prod
  条件: [MulLeftMono α] (f : α -> α) (h : 对任意 x, x in s -> f x <= x)
  证明: prod_le_prod_of_rel_le rel_map_left.2 rel_refl_of_refl_on h

@[to_additive]

Depends on / 依赖: prod_le_prod_of_rel_le, rel_map_left, rel_refl_of_refl_on
-/
lemma prod_map_le_prod [MulLeftMono α] (f : α -> α) (h : forall x, x in s -> f x <= x) :
    (s.map f).prod <= s.prod :=
prod_le_prod_of_rel_le rel_map_left.2 rel_refl_of_refl_on h

@[to_additive]
/--
lemma `prod_le_prod_map` / 引理 `prod_le_prod_map`

English:
lemma prod_le_prod_map
  given: [MulLeftMono α] (f : α -> α) (h : forall x, x in s -> x <= f x)
  proof: prod_map_le_prod (α := αᵒᵈ) f h

@[to_additive card_nsmul_le_sum]

中文:
引理 prod_le_prod_map
  条件: [MulLeftMono α] (f : α -> α) (h : 对任意 x, x in s -> x <= f x)
  证明: prod_map_le_prod (α := αᵒᵈ) f h

@[to_additive card_nsmul_le_sum]

Depends on / 依赖: prod_map_le_prod
-/
lemma prod_le_prod_map [MulLeftMono α] (f : α -> α) (h : forall x, x in s -> x <= f x) :
    s.prod <= (s.map f).prod :=
  prod_map_le_prod (α := αᵒᵈ) f h

@[to_additive card_nsmul_le_sum]
/--
lemma `pow_card_le_prod` / 引理 `pow_card_le_prod`

English:
lemma pow_card_le_prod
  given: [MulLeftMono α] (h : forall x in s, a <= x)
  statement: a ^ card s <= s.prod
  proof: by
  rw [← Multiset.prod_replicate]; rw [← Multiset.map_const]
  exact prod_map_le_prod _ h

中文:
引理 pow_card_le_prod
  条件: [MulLeftMono α] (h : 对任意 x in s, a <= x)
  结论: a ^ card s <= s.乘积
  证明: by
  rw [← Multiset.prod_replicate]; rw [← Multiset.map_const]
  exact prod_map_le_prod _ h

Depends on / 依赖: Multiset, Multiset.map_const, Multiset.prod_replicate, map_const, prod_map_le_prod, prod_replicate
-/
lemma pow_card_le_prod [MulLeftMono α] (h : forall x in s, a <= x) : a ^ card s <= s.prod := by
  rw [← Multiset.prod_replicate]; rw [← Multiset.map_const]
  exact prod_map_le_prod _ h

end OrderedCommMonoid

section
variable [CommMonoid α] [CommMonoid β] [Preorder β] [IsOrderedMonoid β]

@[to_additive le_sum_of_subadditive_on_pred]
/--
lemma `le_prod_of_submultiplicative_on_pred` / 引理 `le_prod_of_submultiplicative_on_pred`

English:
lemma le_prod_of_submultiplicative_on_pred
  statement: (f : α -> β)
  proof: by
  induction s using Quotient.inductionOn with
  | h l => simp [l.le_prod_of_submultiplicative_on_pred f p h_one hp_one h_mul hp_mul (by simpa)]

@[to_additive le_sum_of_subadditive]

中文:
引理 le_prod_of_submultiplicative_on_pred
  结论: (f : α -> β)
  证明: by
  induction s using Quotient.inductionOn with
  | h l => simp [l.le_prod_of_submultiplicative_on_pred f p h_one hp_one h_mul hp_mul (by simpa)]

@[to_additive le_sum_of_subadditive]

Depends on / 依赖: Quotient, Quotient.inductionOn, h_mul, h_one, hp_mul, hp_one, inductionOn, l.le_prod_of_submultiplicative_on_pred, le_prod_of_submultiplicative_on_pred
-/
lemma le_prod_of_submultiplicative_on_pred (f : α -> β)
    (p : α -> Prop) (h_one : f 1 <= 1) (hp_one : p 1)
    (h_mul : forall a b, p a -> p b -> f (a * b) <= f a * f b) (hp_mul : forall a b, p a -> p b -> p (a * b))
    (s : Multiset α) (hps : forall a, a in s -> p a) : f s.prod <= (s.map f).prod := by
  induction s using Quotient.inductionOn with
  | h l => simp [l.le_prod_of_submultiplicative_on_pred f p h_one hp_one h_mul hp_mul (by simpa)]

@[to_additive le_sum_of_subadditive]
/--
lemma `le_prod_of_submultiplicative` / 引理 `le_prod_of_submultiplicative`

English:
lemma le_prod_of_submultiplicative
  statement: (f : α -> β) (h_one : f 1 <= 1)
  proof: by
  induction s using Quotient.inductionOn with
  | h l => simp [l.le_prod_of_submultiplicative f h_one h_mul]

@[to_additive le_sum_nonempty_of_subadditive_on_pred]

中文:
引理 le_prod_of_submultiplicative
  结论: (f : α -> β) (h_one : f 1 <= 1)
  证明: by
  induction s using Quotient.inductionOn with
  | h l => simp [l.le_prod_of_submultiplicative f h_one h_mul]

@[to_additive le_sum_nonempty_of_subadditive_on_pred]

Depends on / 依赖: Quotient, Quotient.inductionOn, h_mul, h_one, inductionOn, l.le_prod_of_submultiplicative, le_prod_of_submultiplicative
-/
lemma le_prod_of_submultiplicative (f : α -> β) (h_one : f 1 <= 1)
    (h_mul : forall a b, f (a * b) <= f a * f b) (s : Multiset α) : f s.prod <= (s.map f).prod := by
  induction s using Quotient.inductionOn with
  | h l => simp [l.le_prod_of_submultiplicative f h_one h_mul]

@[to_additive le_sum_nonempty_of_subadditive_on_pred]
/--
lemma `le_prod_nonempty_of_submultiplicative_on_pred` / 引理 `le_prod_nonempty_of_submultiplicative_on_pred`

English:
lemma le_prod_nonempty_of_submultiplicative_on_pred
  statement: (f : α -> β) (p : α -> Prop)
  proof: by
  induction s using Quotient.inductionOn with
  | h l =>
    simp [l.le_prod_nonempty_of_submultiplicative_on_pred f p h_mul hp_mul
      (by simpa using hs_nonempty) (by simpa)]

@[to_additive le_sum_nonempty_of_subadditive]

中文:
引理 le_prod_nonempty_of_submultiplicative_on_pred
  结论: (f : α -> β) (p : α -> 命题)
  证明: by
  induction s using Quotient.inductionOn with
  | h l =>
    simp [l.le_prod_nonempty_of_submultiplicative_on_pred f p h_mul hp_mul
      (by simpa using hs_nonempty) (by simpa)]

@[to_additive le_sum_nonempty_of_subadditive]

Depends on / 依赖: Quotient, Quotient.inductionOn, h_mul, hp_mul, hs_nonempty, inductionOn, l.le_prod_nonempty_of_submultiplicative_on_pred, le_prod_nonempty_of_submultiplicative_on_pred
-/
lemma le_prod_nonempty_of_submultiplicative_on_pred (f : α -> β) (p : α -> Prop)
    (h_mul : forall a b, p a -> p b -> f (a * b) <= f a * f b) (hp_mul : forall a b, p a -> p b -> p (a * b))
    (s : Multiset α) (hs_nonempty : s != ∅) (hs : forall a, a in s -> p a) : f s.prod <= (s.map f).prod := by
  induction s using Quotient.inductionOn with
  | h l =>
    simp [l.le_prod_nonempty_of_submultiplicative_on_pred f p h_mul hp_mul
      (by simpa using hs_nonempty) (by simpa)]

@[to_additive le_sum_nonempty_of_subadditive]
/--
lemma `le_prod_nonempty_of_submultiplicative` / 引理 `le_prod_nonempty_of_submultiplicative`

English:
lemma le_prod_nonempty_of_submultiplicative
  statement: (f : α -> β) (h_mul : forall a b, f (a * b) <= f a * f b)
  proof: by
  induction s using Quotient.inductionOn with
  | h l => simp [l.le_prod_nonempty_of_submultiplicative f h_mul (by simpa using hs_nonempty)]

中文:
引理 le_prod_nonempty_of_submultiplicative
  结论: (f : α -> β) (h_mul : 对任意 a b, f (a * b) <= f a * f b)
  证明: by
  induction s using Quotient.inductionOn with
  | h l => simp [l.le_prod_nonempty_of_submultiplicative f h_mul (by simpa using hs_nonempty)]

Depends on / 依赖: Quotient, Quotient.inductionOn, h_mul, hs_nonempty, inductionOn, l.le_prod_nonempty_of_submultiplicative, le_prod_nonempty_of_submultiplicative
-/
lemma le_prod_nonempty_of_submultiplicative (f : α -> β) (h_mul : forall a b, f (a * b) <= f a * f b)
    (s : Multiset α) (hs_nonempty : s != ∅) : f s.prod <= (s.map f).prod := by
  induction s using Quotient.inductionOn with
  | h l => simp [l.le_prod_nonempty_of_submultiplicative f h_mul (by simpa using hs_nonempty)]

end

section OrderedCancelCommMonoid
variable [CommMonoid α] [Preorder α] [IsOrderedCancelMonoid α] [MulLeftStrictMono α]
  {s : Multiset ι} {f g : ι -> α}

@[to_additive sum_lt_sum]
/--
lemma `prod_lt_prod'` / 引理 `prod_lt_prod'`

English:
lemma prod_lt_prod'
  given: (hle : forall i in s, f i <= g i) (hlt : exists i in s, f i < g i)
  proof: by
  obtain ⟨l⟩ := s
  simp only [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.prod_coe]
  exact List.prod_lt_prod' f g hle hlt

@[to_additive sum_lt_sum_of_nonempty]

中文:
引理 prod_lt_prod'
  条件: (hle : 对任意 i in s, f i <= g i) (hlt : 存在 i in s, f i < g i)
  证明: by
  obtain ⟨l⟩ := s
  simp only [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.prod_coe]
  exact List.prod_lt_prod' f g hle hlt

@[to_additive sum_lt_sum_of_nonempty]

Depends on / 依赖: List.prod_lt_prod, Multiset, Multiset.map_coe, Multiset.prod_coe, Multiset.quot_mk_to_coe, map_coe, prod_coe, prod_lt_prod, quot_mk_to_coe
-/
lemma prod_lt_prod' (hle : forall i in s, f i <= g i) (hlt : exists i in s, f i < g i) :
    (s.map f).prod < (s.map g).prod := by
  obtain ⟨l⟩ := s
  simp only [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.prod_coe]
  exact List.prod_lt_prod' f g hle hlt

@[to_additive sum_lt_sum_of_nonempty]
/--
lemma `prod_lt_prod_of_nonempty'` / 引理 `prod_lt_prod_of_nonempty'`

English:
lemma prod_lt_prod_of_nonempty'
  given: (hs : s != ∅) (hfg : forall i in s, f i < g i)
  proof: by
  obtain ⟨i, hi⟩ := exists_mem_of_ne_zero hs
  exact prod_lt_prod' (fun i hi => le_of_lt (hfg i hi)) ⟨i, hi, hfg i hi⟩

中文:
引理 prod_lt_prod_of_nonempty'
  条件: (hs : s != ∅) (hfg : 对任意 i in s, f i < g i)
  证明: by
  obtain ⟨i, hi⟩ := exists_mem_of_ne_zero hs
  exact prod_lt_prod' (fun i hi => le_of_lt (hfg i hi)) ⟨i, hi, hfg i hi⟩

Depends on / 依赖: exists_mem_of_ne_zero, le_of_lt, prod_lt_prod
-/
lemma prod_lt_prod_of_nonempty' (hs : s != ∅) (hfg : forall i in s, f i < g i) :
    (s.map f).prod < (s.map g).prod := by
  obtain ⟨i, hi⟩ := exists_mem_of_ne_zero hs
  exact prod_lt_prod' (fun i hi => le_of_lt (hfg i hi)) ⟨i, hi, hfg i hi⟩

end OrderedCancelCommMonoid

section CanonicallyOrderedMul
variable [CommMonoid α] {m : Multiset α} {a : α}

/--
lemma `prod_eq_one_iff` / 引理 `prod_eq_one_iff`

English:
lemma prod_eq_one_iff
  statement: [PartialOrder α] [CanonicallyOrderedMul α]
  proof: Quotient.inductionOn m fun l => by simpa using List.prod_eq_one_iff

中文:
引理 prod_eq_one_iff
  结论: [偏序 α] [典范有序乘法 α]
  证明: Quotient.inductionOn m fun l => by simpa using List.prod_eq_one_iff
-/
@[to_additive] lemma prod_eq_one_iff [PartialOrder α] [CanonicallyOrderedMul α]
    [IsOrderedMonoid α] : m.prod = 1 ↔ forall x in m, x = (1 : α) :=
  Quotient.inductionOn m fun l => by simpa using List.prod_eq_one_iff

/--
lemma `le_prod_of_mem` / 引理 `le_prod_of_mem`

English:
lemma le_prod_of_mem
  given: (ha : a in m) [Preorder α] [CanonicallyOrderedMul α]
  proof: by
  obtain ⟨t, rfl⟩ := exists_cons_of_mem ha
  rw [prod_cons]
  exact _root_.le_mul_right (le_refl a)

中文:
引理 le_prod_of_mem
  条件: (ha : a in m) [预序 α] [典范有序乘法 α]
  证明: by
  obtain ⟨t, rfl⟩ := exists_cons_of_mem ha
  rw [prod_cons]
  exact _root_.le_mul_right (le_refl a)
-/
@[to_additive] lemma le_prod_of_mem (ha : a in m) [Preorder α] [CanonicallyOrderedMul α] :
    a <= m.prod := by
  obtain ⟨t, rfl⟩ := exists_cons_of_mem ha
  rw [prod_cons]
  exact _root_.le_mul_right (le_refl a)

end CanonicallyOrderedMul

/--
lemma `max_le_of_forall_le` / 引理 `max_le_of_forall_le`

English:
lemma max_le_of_forall_le
  statement: {α : Type*} [LinearOrder α] [OrderBot α] (l : Multiset α)
  proof: by
  induction l using Quotient.inductionOn
  simpa using List.max_le_of_forall_le _ _ h

@[to_additive]

中文:
引理 max_le_of_对任意_le
  结论: {α : 类型} [线性序 α] [有底序 α] (l : Multiset α)
  证明: by
  induction l using Quotient.inductionOn
  simpa using List.max_le_of_forall_le _ _ h

@[to_additive]

Depends on / 依赖: List.max_le_of_forall_le, Quotient, Quotient.inductionOn, inductionOn, max_le_of_forall_le
-/
lemma max_le_of_forall_le {α : Type*} [LinearOrder α] [OrderBot α] (l : Multiset α)
    (n : α) (h : forall x in l, x <= n) : l.fold max ⊥ <= n := by
  induction l using Quotient.inductionOn
  simpa using List.max_le_of_forall_le _ _ h

@[to_additive]
/--
lemma `max_prod_le` / 引理 `max_prod_le`

English:
lemma max_prod_le
  statement: [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α]
  proof: by
  obtain ⟨l⟩ := s
  simp_rw [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.prod_coe]
  apply List.max_prod_le

@[to_additive]

中文:
引理 max_prod_le
  结论: [交换幺半群 α] [线性序 α] [是Ordered幺半群 α]
  证明: by
  obtain ⟨l⟩ := s
  simp_rw [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.prod_coe]
  apply List.max_prod_le

@[to_additive]

Depends on / 依赖: List.max_prod_le, Multiset, Multiset.map_coe, Multiset.prod_coe, Multiset.quot_mk_to_coe, map_coe, max_prod_le, prod_coe, quot_mk_to_coe, simp_rw
-/
lemma max_prod_le [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α]
    {s : Multiset ι} {f g : ι -> α} :
    max (s.map f).prod (s.map g).prod <= (s.map fun i => max (f i) (g i)).prod := by
  obtain ⟨l⟩ := s
  simp_rw [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.prod_coe]
  apply List.max_prod_le

@[to_additive]
/--
lemma `prod_min_le` / 引理 `prod_min_le`

English:
lemma prod_min_le
  statement: [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α]
  proof: by
  obtain ⟨l⟩ := s
  simp_rw [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.prod_coe]
  apply List.prod_min_le

中文:
引理 prod_min_le
  结论: [交换幺半群 α] [线性序 α] [是Ordered幺半群 α]
  证明: by
  obtain ⟨l⟩ := s
  simp_rw [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.prod_coe]
  apply List.prod_min_le

Depends on / 依赖: List.prod_min_le, Multiset, Multiset.map_coe, Multiset.prod_coe, Multiset.quot_mk_to_coe, map_coe, prod_coe, prod_min_le, quot_mk_to_coe, simp_rw
-/
lemma prod_min_le [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α]
    {s : Multiset ι} {f g : ι -> α} :
    (s.map fun i => min (f i) (g i)).prod <= min (s.map f).prod (s.map g).prod := by
  obtain ⟨l⟩ := s
  simp_rw [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.prod_coe]
  apply List.prod_min_le

/--
lemma `abs_sum_le_sum_abs` / 引理 `abs_sum_le_sum_abs`

English:
lemma abs_sum_le_sum_abs
  given: [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {s : Multiset α}
  proof: le_sum_of_subadditive _ abs_zero.le abs_add_le s

中文:
引理 abs_sum_le_sum_abs
  条件: [加法交换群 α] [线性序 α] [是OrderedAdd幺半群 α] {s : Multiset α}
  证明: le_sum_of_subadditive _ abs_zero.le abs_add_le s

Depends on / 依赖: abs_add_le, abs_zero, abs_zero.le, le_sum_of_subadditive
-/
lemma abs_sum_le_sum_abs [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {s : Multiset α} :
    |s.sum| <= (s.map abs).sum :=
  le_sum_of_subadditive _ abs_zero.le abs_add_le s

section ProdSum

variable [CommMonoid α] [AddCommMonoid β] [Preorder β] [AddLeftMono β] (m : Multiset α) (f : α -> β)

/--
lemma `apply_prod_le_sum_map` / 引理 `apply_prod_le_sum_map`

English:
lemma apply_prod_le_sum_map
  given: (h_one : f 1 <= 0) (h_mul : forall (a b : α), f (a * b) <= f a + f b)
  proof: by
  induction m using Quotient.inductionOn with
  | h l => simp [l.apply_prod_le_sum_map _ h_one h_mul]

中文:
引理 apply_prod_le_sum_map
  条件: (h_one : f 1 <= 0) (h_mul : 对任意 (a b : α), f (a * b) <= f a + f b)
  证明: by
  induction m using Quotient.inductionOn with
  | h l => simp [l.apply_prod_le_sum_map _ h_one h_mul]

Depends on / 依赖: Quotient, Quotient.inductionOn, apply_prod_le_sum_map, h_mul, h_one, inductionOn, l.apply_prod_le_sum_map
-/
lemma apply_prod_le_sum_map (h_one : f 1 <= 0) (h_mul : forall (a b : α), f (a * b) <= f a + f b) :
    f m.prod <= (m.map f).sum := by
  induction m using Quotient.inductionOn with
  | h l => simp [l.apply_prod_le_sum_map _ h_one h_mul]

/--
lemma `sum_map_le_apply_prod` / 引理 `sum_map_le_apply_prod`

English:
lemma sum_map_le_apply_prod
  given: (h_one : 0 <= f 1) (h_mul : forall (a b : α), f a + f b <= f (a * b))
  proof: m.apply_prod_le_sum_map (β := βᵒᵈ) f h_one h_mul

中文:
引理 sum_map_le_apply_prod
  条件: (h_one : 0 <= f 1) (h_mul : 对任意 (a b : α), f a + f b <= f (a * b))
  证明: m.apply_prod_le_sum_map (β := βᵒᵈ) f h_one h_mul

Depends on / 依赖: apply_prod_le_sum_map, h_mul, h_one, m.apply_prod_le_sum_map
-/
lemma sum_map_le_apply_prod (h_one : 0 <= f 1) (h_mul : forall (a b : α), f a + f b <= f (a * b)) :
    (m.map f).sum <= f m.prod :=
  m.apply_prod_le_sum_map (β := βᵒᵈ) f h_one h_mul

end ProdSum

end Multiset
