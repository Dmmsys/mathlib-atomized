/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.OrderDual
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Big operators on a list in ordered groups

This file contains the results concerning the interaction of list big operators with ordered
groups/monoids.
-/

public section

variable {ι α M N : Type*}

namespace List
section Monoid
variable [Monoid M]

@[to_additive sum_le_sum]
/--
lemma `Forall₂.prod_le_prod'` / 引理 `Forall₂.prod_le_prod'`

English:
lemma Forall₂.prod_le_prod'
  statement: [Preorder M] [MulRightMono M]
  proof: by
  induction h with
  | nil => rfl
  | cons hab ih ih' => simpa only [prod_cons] using mul_le_mul' hab ih'

中文:
引理 Forall₂.prod_le_prod'
  结论: [预序 M] [MulRightMono M]
  证明: by
  induction h with
  | nil => rfl
  | cons hab ih ih' => simpa only [prod_cons] using mul_le_mul' hab ih'

Depends on / 依赖: mul_le_mul, prod_cons
-/
lemma Forall₂.prod_le_prod' [Preorder M] [MulRightMono M]
    [MulLeftMono M] {l₁ l₂ : List M} (h : Forall₂ (· <= ·) l₁ l₂) :
    l₁.prod <= l₂.prod := by
  induction h with
  | nil => rfl
  | cons hab ih ih' => simpa only [prod_cons] using mul_le_mul' hab ih'

/-- If `l₁` is a sublist of `l₂` and all elements of `l₂` are greater than or equal to one, then
`l₁.prod ≤ l₂.prod`. One can prove a stronger version assuming `∀ a ∈ l₂.diff l₁, 1 ≤ a` instead
of `∀ a ∈ l₂, 1 ≤ a` but this lemma is not yet in `mathlib`. -/
@[to_additive sum_le_sum /-- If `l₁` is a sublist of `l₂` and all elements of `l₂` are nonnegative,
  then `l₁.sum ≤ l₂.sum`.
  One can prove a stronger version assuming `∀ a ∈ l₂.diff l₁, 0 ≤ a` instead of `∀ a ∈ l₂, 0 ≤ a`
  but this lemma is not yet in `mathlib`. -/]
/--
lemma `Sublist.prod_le_prod'` / 引理 `Sublist.prod_le_prod'`

English:
lemma Sublist.prod_le_prod'
  statement: [Preorder M] [MulRightMono M]
  proof: by
  induction h with
  | slnil => rfl
  | cons a _ ih' =>
    simp only [prod_cons, forall_mem_cons] at h₁ ⊢
    exact (ih' h₁.2).trans (le_mul_of_one_le_left' h₁.1)
  | cons_cons a _ ih' =>
    simp only [prod_cons, forall_mem_cons] at h₁ ⊢
    grw [ih' h₁.2]

@[to_additive sum_le_sum]

中文:
引理 子表.prod_le_prod'
  结论: [预序 M] [MulRightMono M]
  证明: by
  induction h with
  | slnil => rfl
  | cons a _ ih' =>
    simp only [prod_cons, forall_mem_cons] at h₁ ⊢
    exact (ih' h₁.2).trans (le_mul_of_one_le_left' h₁.1)
  | cons_cons a _ ih' =>
    simp only [prod_cons, forall_mem_cons] at h₁ ⊢
    grw [ih' h₁.2]

@[to_additive sum_le_sum]

Depends on / 依赖: cons_cons, forall_mem_cons, le_mul_of_one_le_left, prod_cons
-/
lemma Sublist.prod_le_prod' [Preorder M] [MulRightMono M]
    [MulLeftMono M] {l₁ l₂ : List M} (h : l₁ <+ l₂)
    (h₁ : forall a in l₂, (1 : M) <= a) : l₁.prod <= l₂.prod := by
  induction h with
  | slnil => rfl
  | cons a _ ih' =>
    simp only [prod_cons, forall_mem_cons] at h₁ ⊢
    exact (ih' h₁.2).trans (le_mul_of_one_le_left' h₁.1)
  | cons_cons a _ ih' =>
    simp only [prod_cons, forall_mem_cons] at h₁ ⊢
    grw [ih' h₁.2]

@[to_additive sum_le_sum]
/--
lemma `SublistForall₂.prod_le_prod'` / 引理 `SublistForall₂.prod_le_prod'`

English:
lemma SublistForall₂.prod_le_prod'
  statement: [Preorder M]
  proof: let ⟨_, hall, hsub⟩ := sublistForall₂_iff.1 h
hall.prod_le_prod'.trans hsub.prod_le_prod' h₁

@[to_additive sum_le_sum]

中文:
引理 SublistForall₂.prod_le_prod'
  结论: [预序 M]
  证明: let ⟨_, hall, hsub⟩ := sublistForall₂_iff.1 h
hall.prod_le_prod'.trans hsub.prod_le_prod' h₁

@[to_additive sum_le_sum]

Depends on / 依赖: hall.prod_le_prod, hsub.prod_le_prod, prod_le_prod
-/
lemma SublistForall₂.prod_le_prod' [Preorder M]
    [MulRightMono M] [MulLeftMono M]
    {l₁ l₂ : List M} (h : SublistForall₂ (· <= ·) l₁ l₂) (h₁ : forall a in l₂, (1 : M) <= a) :
    l₁.prod <= l₂.prod :=
  let ⟨_, hall, hsub⟩ := sublistForall₂_iff.1 h
hall.prod_le_prod'.trans hsub.prod_le_prod' h₁

@[to_additive sum_le_sum]
/--
lemma `prod_le_prod'` / 引理 `prod_le_prod'`

English:
lemma prod_le_prod'
  statement: [Preorder M] [MulRightMono M]
  proof: Forall₂.prod_le_prod' by simpa

@[to_additive sum_lt_sum]

中文:
引理 prod_le_prod'
  结论: [预序 M] [MulRightMono M]
  证明: Forall₂.prod_le_prod' by simpa

@[to_additive sum_lt_sum]

Depends on / 依赖: prod_le_prod
-/
lemma prod_le_prod' [Preorder M] [MulRightMono M]
    [MulLeftMono M] {l : List ι} {f g : ι -> M} (h : forall i in l, f i <= g i) :
    (l.map f).prod <= (l.map g).prod :=
Forall₂.prod_le_prod' by simpa

@[to_additive sum_lt_sum]
/--
lemma `prod_lt_prod'` / 引理 `prod_lt_prod'`

English:
lemma prod_lt_prod'
  statement: [Preorder M] [MulLeftStrictMono M]
  proof: by
  induction l with
  | nil => simp at h₂
  | cons i l ihl =>
    simp only [forall_mem_cons, map_cons, prod_cons] at h₁ ⊢
    simp only [mem_cons, exists_eq_or_imp] at h₂
    cases h₂
    · exact mul_lt_mul_of_lt_of_le ‹_› (prod_le_prod' h₁.2)
· exact mul_lt_mul_of_le_of_lt h₁.1 ihl h₁.2 ‹_›

@[t

中文:
引理 prod_lt_prod'
  结论: [预序 M] [MulLeftStrictMono M]
  证明: by
  induction l with
  | nil => simp at h₂
  | cons i l ihl =>
    simp only [forall_mem_cons, map_cons, prod_cons] at h₁ ⊢
    simp only [mem_cons, exists_eq_or_imp] at h₂
    cases h₂
    · exact mul_lt_mul_of_lt_of_le ‹_› (prod_le_prod' h₁.2)
· exact mul_lt_mul_of_le_of_lt h₁.1 ihl h₁.2 ‹_›

@[t

Depends on / 依赖: exists_eq_or_imp, forall_mem_cons, map_cons, mem_cons, mul_lt_mul_of_le_of_lt, mul_lt_mul_of_lt_of_le, prod_cons, prod_le_prod
-/
lemma prod_lt_prod' [Preorder M] [MulLeftStrictMono M]
    [MulLeftMono M] [MulRightStrictMono M]
    [MulRightMono M] {l : List ι} (f g : ι -> M)
    (h₁ : forall i in l, f i <= g i) (h₂ : exists i in l, f i < g i) : (l.map f).prod < (l.map g).prod := by
  induction l with
  | nil => simp at h₂
  | cons i l ihl =>
    simp only [forall_mem_cons, map_cons, prod_cons] at h₁ ⊢
    simp only [mem_cons, exists_eq_or_imp] at h₂
    cases h₂
    · exact mul_lt_mul_of_lt_of_le ‹_› (prod_le_prod' h₁.2)
· exact mul_lt_mul_of_le_of_lt h₁.1 ihl h₁.2 ‹_›

@[to_additive]
/--
lemma `prod_lt_prod_of_ne_nil` / 引理 `prod_lt_prod_of_ne_nil`

English:
lemma prod_lt_prod_of_ne_nil
  statement: [Preorder M] [MulLeftStrictMono M]
  proof: (prod_lt_prod' f g fun i hi => (hlt i hi).le)
    (exists_mem_of_ne_nil l hl).imp fun i hi => ⟨hi, hlt i hi⟩

@[to_additive sum_le_card_nsmul]

中文:
引理 prod_lt_prod_of_ne_nil
  结论: [预序 M] [MulLeftStrictMono M]
  证明: (prod_lt_prod' f g fun i hi => (hlt i hi).le)
    (exists_mem_of_ne_nil l hl).imp fun i hi => ⟨hi, hlt i hi⟩

@[to_additive sum_le_card_nsmul]

Depends on / 依赖: exists_mem_of_ne_nil, prod_lt_prod
-/
lemma prod_lt_prod_of_ne_nil [Preorder M] [MulLeftStrictMono M]
    [MulLeftMono M] [MulRightStrictMono M]
    [MulRightMono M] {l : List ι} (hl : l != []) (f g : ι -> M)
    (hlt : forall i in l, f i < g i) : (l.map f).prod < (l.map g).prod :=
(prod_lt_prod' f g fun i hi => (hlt i hi).le)
    (exists_mem_of_ne_nil l hl).imp fun i hi => ⟨hi, hlt i hi⟩

@[to_additive sum_le_card_nsmul]
/--
lemma `prod_le_pow_card` / 引理 `prod_le_pow_card`

English:
lemma prod_le_pow_card
  statement: [Preorder M] [MulRightMono M]
  proof: by
  simpa only [map_id', map_const', prod_replicate] using prod_le_prod' h

@[to_additive card_nsmul_le_sum]

中文:
引理 prod_le_pow_card
  结论: [预序 M] [MulRightMono M]
  证明: by
  simpa only [map_id', map_const', prod_replicate] using prod_le_prod' h

@[to_additive card_nsmul_le_sum]

Depends on / 依赖: map_const, map_id, prod_le_prod, prod_replicate
-/
lemma prod_le_pow_card [Preorder M] [MulRightMono M]
    [MulLeftMono M] (l : List M) (n : M) (h : forall x in l, x <= n) :
    l.prod <= n ^ l.length := by
  simpa only [map_id', map_const', prod_replicate] using prod_le_prod' h

@[to_additive card_nsmul_le_sum]
/--
lemma `pow_card_le_prod` / 引理 `pow_card_le_prod`

English:
lemma pow_card_le_prod
  statement: [Preorder M] [MulRightMono M]
  proof: @prod_le_pow_card Mᵒᵈ _ _ _ _ l n h

@[to_additive exists_lt_of_sum_lt]

中文:
引理 pow_card_le_prod
  结论: [预序 M] [MulRightMono M]
  证明: @prod_le_pow_card Mᵒᵈ _ _ _ _ l n h

@[to_additive exists_lt_of_sum_lt]

Depends on / 依赖: prod_le_pow_card
-/
lemma pow_card_le_prod [Preorder M] [MulRightMono M]
    [MulLeftMono M] (l : List M) (n : M) (h : forall x in l, n <= x) :
    n ^ l.length <= l.prod :=
  @prod_le_pow_card Mᵒᵈ _ _ _ _ l n h

@[to_additive exists_lt_of_sum_lt]
/--
lemma `exists_lt_of_prod_lt'` / 引理 `exists_lt_of_prod_lt'`

English:
lemma exists_lt_of_prod_lt'
  statement: [LinearOrder M] [MulRightMono M]
  proof: by
  contrapose! h
  exact prod_le_prod' h

@[to_additive exists_le_of_sum_le]

中文:
引理 存在_lt_of_prod_lt'
  结论: [线性序 M] [MulRightMono M]
  证明: by
  contrapose! h
  exact prod_le_prod' h

@[to_additive exists_le_of_sum_le]

Depends on / 依赖: contrapose, prod_le_prod
-/
lemma exists_lt_of_prod_lt' [LinearOrder M] [MulRightMono M]
    [MulLeftMono M] {l : List ι} (f g : ι -> M)
    (h : (l.map f).prod < (l.map g).prod) : exists i in l, f i < g i := by
  contrapose! h
  exact prod_le_prod' h

@[to_additive exists_le_of_sum_le]
/--
lemma `exists_le_of_prod_le'` / 引理 `exists_le_of_prod_le'`

English:
lemma exists_le_of_prod_le'
  statement: [LinearOrder M] [MulLeftStrictMono M]
  proof: by
  contrapose! h
  exact prod_lt_prod_of_ne_nil hl _ _ h

@[to_additive sum_nonneg]

中文:
引理 存在_le_of_prod_le'
  结论: [线性序 M] [MulLeftStrictMono M]
  证明: by
  contrapose! h
  exact prod_lt_prod_of_ne_nil hl _ _ h

@[to_additive sum_nonneg]

Depends on / 依赖: contrapose, prod_lt_prod_of_ne_nil
-/
lemma exists_le_of_prod_le' [LinearOrder M] [MulLeftStrictMono M]
    [MulLeftMono M] [MulRightStrictMono M]
    [MulRightMono M] {l : List ι} (hl : l != []) (f g : ι -> M)
    (h : (l.map f).prod <= (l.map g).prod) : exists x in l, f x <= g x := by
  contrapose! h
  exact prod_lt_prod_of_ne_nil hl _ _ h

@[to_additive sum_nonneg]
/--
lemma `one_le_prod_of_one_le` / 引理 `one_le_prod_of_one_le`

English:
lemma one_le_prod_of_one_le
  statement: [Preorder M] [MulLeftMono M] {l : List M}
  proof: by
  -- We don't use `pow_card_le_prod` to avoid assumption
  -- [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)]
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [prod_cons]
    exact one_le_mul (hl₁ hd mem_cons_self) (ih fun x h => hl₁ x (mem_cons_of_mem hd h))

@[to_additive]

中文:
引理 one_le_prod_of_one_le
  结论: [预序 M] [MulLeftMono M] {l : 列表 M}
  证明: by
  -- We don't use `pow_card_le_prod` to avoid assumption
  -- [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)]
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [prod_cons]
    exact one_le_mul (hl₁ hd mem_cons_self) (ih fun x h => hl₁ x (mem_cons_of_mem hd h))

@[to_additive]
-/
lemma one_le_prod_of_one_le [Preorder M] [MulLeftMono M] {l : List M}
    (hl₁ : forall x in l, (1 : M) <= x) : 1 <= l.prod := by
  -- We don't use `pow_card_le_prod` to avoid assumption
  -- [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)]
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [prod_cons]
    exact one_le_mul (hl₁ hd mem_cons_self) (ih fun x h => hl₁ x (mem_cons_of_mem hd h))

@[to_additive]
/--
lemma `max_prod_le` / 引理 `max_prod_le`

English:
lemma max_prod_le
  statement: (l : List α) (f g : α -> M) [LinearOrder M]
  proof: by
  rw [max_le_iff]
  constructor <;> apply List.prod_le_prod' <;> intros
  · apply le_max_left
  · apply le_max_right

@[to_additive]

中文:
引理 max_prod_le
  结论: (l : 列表 α) (f g : α -> M) [线性序 M]
  证明: by
  rw [max_le_iff]
  constructor <;> apply List.prod_le_prod' <;> intros
  · apply le_max_left
  · apply le_max_right

@[to_additive]

Depends on / 依赖: List.prod_le_prod, intros, le_max_left, le_max_right, max_le_iff, prod_le_prod
-/
lemma max_prod_le (l : List α) (f g : α -> M) [LinearOrder M]
    [MulLeftMono M] [MulRightMono M] :
    max (l.map f).prod (l.map g).prod <= (l.map fun i => max (f i) (g i)).prod := by
  rw [max_le_iff]
  constructor <;> apply List.prod_le_prod' <;> intros
  · apply le_max_left
  · apply le_max_right

@[to_additive]
/--
lemma `prod_min_le` / 引理 `prod_min_le`

English:
lemma prod_min_le
  statement: [LinearOrder M] [MulLeftMono M]
  proof: by
  rw [le_min_iff]
  constructor <;> apply List.prod_le_prod' <;> intros
  · apply min_le_left
  · apply min_le_right

中文:
引理 prod_min_le
  结论: [线性序 M] [MulLeftMono M]
  证明: by
  rw [le_min_iff]
  constructor <;> apply List.prod_le_prod' <;> intros
  · apply min_le_left
  · apply min_le_right

Depends on / 依赖: List.prod_le_prod, intros, le_min_iff, min_le_left, min_le_right, prod_le_prod
-/
lemma prod_min_le [LinearOrder M] [MulLeftMono M]
    [MulRightMono M] (l : List α) (f g : α -> M) :
    (l.map fun i => min (f i) (g i)).prod <= min (l.map f).prod (l.map g).prod := by
  rw [le_min_iff]
  constructor <;> apply List.prod_le_prod' <;> intros
  · apply min_le_left
  · apply min_le_right

variable [Preorder M] [CanonicallyOrderedMul M]

/--
lemma `monotone_prod_take` / 引理 `monotone_prod_take`

English:
lemma monotone_prod_take
  given: (L : List M)
  statement: Monotone fun i => (L.take i).prod
  proof: by
  refine monotone_nat_of_le_succ fun n => ?_
  rcases lt_or_ge n L.length with h | h
  · rw [prod_take_succ _ _ h]
    exact le_self_mul
  · simp [take_of_length_le h, take_of_length_le (le_trans h (Nat.le_succ _))]

中文:
引理 monotone_prod_take
  条件: (L : 列表 M)
  结论: 递增 fun i => (L.take i).乘积
  证明: by
  refine monotone_nat_of_le_succ fun n => ?_
  rcases lt_or_ge n L.length with h | h
  · rw [prod_take_succ _ _ h]
    exact le_self_mul
  · simp [take_of_length_le h, take_of_length_le (le_trans h (Nat.le_succ _))]
-/
@[to_additive] lemma monotone_prod_take (L : List M) : Monotone fun i => (L.take i).prod := by
  refine monotone_nat_of_le_succ fun n => ?_
  rcases lt_or_ge n L.length with h | h
  · rw [prod_take_succ _ _ h]
    exact le_self_mul
  · simp [take_of_length_le h, take_of_length_le (le_trans h (Nat.le_succ _))]

/-- See also `List.single_le_prod`. -/
@[to_additive /-- See also `List.single_le_sum`. -/]
/--
theorem `le_prod_of_mem` / 定理 `le_prod_of_mem`

English:
theorem le_prod_of_mem
  given: {xs : List M} {x : M} (h₁ : x in xs)
  statement: x <= xs.prod
  proof: by
  induction xs with
  | nil => simp at h₁
  | cons y ys ih =>
    simp only [mem_cons] at h₁
    rcases h₁ with (rfl | h₁)
    · simp
    · specialize ih h₁
      simp only [List.prod_cons]
      exact le_mul_left ih

中文:
定理 le_prod_of_mem
  条件: {xs : 列表 M} {x : M} (h₁ : x in xs)
  结论: x <= xs.乘积
  证明: by
  induction xs with
  | nil => simp at h₁
  | cons y ys ih =>
    simp only [mem_cons] at h₁
    rcases h₁ with (rfl | h₁)
    · simp
    · specialize ih h₁
      simp only [List.prod_cons]
      exact le_mul_left ih

Depends on / 依赖: List.prod_cons, le_mul_left, mem_cons, prod_cons, specialize
-/
theorem le_prod_of_mem {xs : List M} {x : M} (h₁ : x in xs) : x <= xs.prod := by
  induction xs with
  | nil => simp at h₁
  | cons y ys ih =>
    simp only [mem_cons] at h₁
    rcases h₁ with (rfl | h₁)
    · simp
    · specialize ih h₁
      simp only [List.prod_cons]
      exact le_mul_left ih

end Monoid

section
variable {α β : Type*} [Monoid α] [CommMonoid β] [Preorder β] [IsOrderedMonoid β]

@[to_additive le_sum_of_subadditive_on_pred]
/--
lemma `le_prod_of_submultiplicative_on_pred` / 引理 `le_prod_of_submultiplicative_on_pred`

English:
lemma le_prod_of_submultiplicative_on_pred
  statement: (f : α -> β)
  proof: by
  induction l with
  | nil => simp [h_one]
  | cons a s ih =>
    have hpla : forall x, x in s -> p x := fun x hx => hpl x (mem_cons_of_mem _ hx)
    have hp_prod : p s.prod := prod_induction p hp_mul hp_one hpla
    grw [prod_cons, map_cons, prod_cons, h_mul a s.prod (hpl _ mem_cons_self) hp_pro

中文:
引理 le_prod_of_submultiplicative_on_pred
  结论: (f : α -> β)
  证明: by
  induction l with
  | nil => simp [h_one]
  | cons a s ih =>
    have hpla : forall x, x in s -> p x := fun x hx => hpl x (mem_cons_of_mem _ hx)
    have hp_prod : p s.prod := prod_induction p hp_mul hp_one hpla
    grw [prod_cons, map_cons, prod_cons, h_mul a s.prod (hpl _ mem_cons_self) hp_pro

Depends on / 依赖: h_mul, h_one, hp_mul, hp_one, hp_prod, map_cons, mem_cons_of_mem, mem_cons_self, prod_cons, prod_induction, s.prod
-/
lemma le_prod_of_submultiplicative_on_pred (f : α -> β)
    (p : α -> Prop) (h_one : f 1 <= 1) (hp_one : p 1)
    (h_mul : forall a b, p a -> p b -> f (a * b) <= f a * f b) (hp_mul : forall a b, p a -> p b -> p (a * b))
    (l : List α) (hpl : forall a, a in l -> p a) : f l.prod <= (l.map f).prod := by
  induction l with
  | nil => simp [h_one]
  | cons a s ih =>
    have hpla : forall x, x in s -> p x := fun x hx => hpl x (mem_cons_of_mem _ hx)
    have hp_prod : p s.prod := prod_induction p hp_mul hp_one hpla
    grw [prod_cons, map_cons, prod_cons, h_mul a s.prod (hpl _ mem_cons_self) hp_prod, ih hpla]

@[to_additive le_sum_of_subadditive]
/--
lemma `le_prod_of_submultiplicative` / 引理 `le_prod_of_submultiplicative`

English:
lemma le_prod_of_submultiplicative
  statement: (f : α -> β) (h_one : f 1 <= 1)
  proof: le_prod_of_submultiplicative_on_pred f (fun _ => True) h_one trivial (fun x y _ _ => h_mul x y)
    (by simp) l (by simp)

@[to_additive le_sum_nonempty_of_subadditive_on_pred]

中文:
引理 le_prod_of_submultiplicative
  结论: (f : α -> β) (h_one : f 1 <= 1)
  证明: le_prod_of_submultiplicative_on_pred f (fun _ => True) h_one trivial (fun x y _ _ => h_mul x y)
    (by simp) l (by simp)

@[to_additive le_sum_nonempty_of_subadditive_on_pred]

Depends on / 依赖: h_mul, h_one, le_prod_of_submultiplicative_on_pred
-/
lemma le_prod_of_submultiplicative (f : α -> β) (h_one : f 1 <= 1)
    (h_mul : forall a b, f (a * b) <= f a * f b) (l : List α) : f l.prod <= (l.map f).prod :=
  le_prod_of_submultiplicative_on_pred f (fun _ => True) h_one trivial (fun x y _ _ => h_mul x y)
    (by simp) l (by simp)

@[to_additive le_sum_nonempty_of_subadditive_on_pred]
/--
lemma `le_prod_nonempty_of_submultiplicative_on_pred` / 引理 `le_prod_nonempty_of_submultiplicative_on_pred`

English:
lemma le_prod_nonempty_of_submultiplicative_on_pred
  statement: (f : α -> β) (p : α -> Prop)
  proof: by
  induction l with
  | nil => simp at hl_nonempty
  | cons a l ih =>
    rw [prod_cons]; rw [map_cons]; rw [prod_cons]
    by_cases hl_empty : l = []
    · simp [hl_empty]
    have hla_restrict : forall x, x in l -> p x := fun x hx => hl x (mem_cons_of_mem _ hx)
    have hp_sup : p l.prod := prod

中文:
引理 le_prod_nonempty_of_submultiplicative_on_pred
  结论: (f : α -> β) (p : α -> 命题)
  证明: by
  induction l with
  | nil => simp at hl_nonempty
  | cons a l ih =>
    rw [prod_cons]; rw [map_cons]; rw [prod_cons]
    by_cases hl_empty : l = []
    · simp [hl_empty]
    have hla_restrict : forall x, x in l -> p x := fun x hx => hl x (mem_cons_of_mem _ hx)
    have hp_sup : p l.prod := prod

Depends on / 依赖: h_mul, hl_empty, hl_nonempty, hla_restrict, hp_a, hp_mul, hp_sup, l.prod, map_cons, mem_cons_of_mem, mem_cons_self, prod_cons, prod_induction_nonempty
-/
lemma le_prod_nonempty_of_submultiplicative_on_pred (f : α -> β) (p : α -> Prop)
    (h_mul : forall a b, p a -> p b -> f (a * b) <= f a * f b) (hp_mul : forall a b, p a -> p b -> p (a * b))
    (l : List α) (hl_nonempty : l != []) (hl : forall a, a in l -> p a) : f l.prod <= (l.map f).prod := by
  induction l with
  | nil => simp at hl_nonempty
  | cons a l ih =>
    rw [prod_cons]; rw [map_cons]; rw [prod_cons]
    by_cases hl_empty : l = []
    · simp [hl_empty]
    have hla_restrict : forall x, x in l -> p x := fun x hx => hl x (mem_cons_of_mem _ hx)
    have hp_sup : p l.prod := prod_induction_nonempty p hp_mul hl_empty hla_restrict
    have hp_a : p a := hl a mem_cons_self
    grw [h_mul a _ hp_a hp_sup, ← ih hl_empty hla_restrict]

@[to_additive le_sum_nonempty_of_subadditive]
/--
lemma `le_prod_nonempty_of_submultiplicative` / 引理 `le_prod_nonempty_of_submultiplicative`

English:
lemma le_prod_nonempty_of_submultiplicative
  statement: (f : α -> β) (h_mul : forall a b, f (a * b) <= f a * f b)
  proof: le_prod_nonempty_of_submultiplicative_on_pred f (fun _ => True) (by simp [h_mul]) (by simp) l
    hs_nonempty (by simp)

中文:
引理 le_prod_nonempty_of_submultiplicative
  结论: (f : α -> β) (h_mul : 对任意 a b, f (a * b) <= f a * f b)
  证明: le_prod_nonempty_of_submultiplicative_on_pred f (fun _ => True) (by simp [h_mul]) (by simp) l
    hs_nonempty (by simp)

Depends on / 依赖: h_mul, hs_nonempty, le_prod_nonempty_of_submultiplicative_on_pred
-/
lemma le_prod_nonempty_of_submultiplicative (f : α -> β) (h_mul : forall a b, f (a * b) <= f a * f b)
    (l : List α) (hs_nonempty : l != ∅) : f l.prod <= (l.map f).prod :=
  le_prod_nonempty_of_submultiplicative_on_pred f (fun _ => True) (by simp [h_mul]) (by simp) l
    hs_nonempty (by simp)

end

-- TODO: develop theory of tropical rings
/--
lemma `sum_le_foldr_max` / 引理 `sum_le_foldr_max`

English:
lemma sum_le_foldr_max
  statement: [AddZeroClass M] [Zero N] [LinearOrder N] (f : M -> N) (h0 : f 0 <= 0)
  proof: by
  induction l with
  | nil => simpa using h0
  | cons hd tl IH =>
    simp only [List.sum_cons, List.foldr_map, List.foldr] at IH ⊢
    exact (hadd _ _).trans (max_le_max le_rfl IH)

@[to_additive sum_pos]

中文:
引理 sum_le_foldr_max
  结论: [加法零类 M] [零 N] [线性序 N] (f : M -> N) (h0 : f 0 <= 0)
  证明: by
  induction l with
  | nil => simpa using h0
  | cons hd tl IH =>
    simp only [List.sum_cons, List.foldr_map, List.foldr] at IH ⊢
    exact (hadd _ _).trans (max_le_max le_rfl IH)

@[to_additive sum_pos]

Depends on / 依赖: List.foldr, List.foldr_map, List.sum_cons, foldr_map, le_rfl, max_le_max, sum_cons
-/
lemma sum_le_foldr_max [AddZeroClass M] [Zero N] [LinearOrder N] (f : M -> N) (h0 : f 0 <= 0)
    (hadd : forall x y, f (x + y) <= max (f x) (f y)) (l : List M) : f l.sum <= (l.map f).foldr max 0 := by
  induction l with
  | nil => simpa using h0
  | cons hd tl IH =>
    simp only [List.sum_cons, List.foldr_map, List.foldr] at IH ⊢
    exact (hadd _ _).trans (max_le_max le_rfl IH)

@[to_additive sum_pos]
/--
lemma `one_lt_prod_of_one_lt` / 引理 `one_lt_prod_of_one_lt`

English:
lemma one_lt_prod_of_one_lt
  given: [CommMonoid M] [Preorder M] [IsOrderedMonoid M]

中文:
引理 one_lt_prod_of_one_lt
  条件: [交换幺半群 M] [预序 M] [是Ordered幺半群 M]
-/
lemma one_lt_prod_of_one_lt [CommMonoid M] [Preorder M] [IsOrderedMonoid M] :
    forall l : List M, (forall x in l, (1 : M) < x) -> l != [] -> 1 < l.prod
  | [], _, h => (h rfl).elim
  | [b], h, _ => by simpa using h
  | a :: b :: l, hl₁, _ => by
    simp only [forall_eq_or_imp, List.mem_cons] at hl₁
    rw [List.prod_cons]
    apply one_lt_mul_of_lt_of_le' hl₁.1
    apply le_of_lt ((b :: l).one_lt_prod_of_one_lt _ (l.cons_ne_nil b))
    grind

/-- See also `List.le_prod_of_mem`. -/
@[to_additive /-- See also `List.le_sum_of_mem`. -/]
/--
lemma `single_le_prod` / 引理 `single_le_prod`

English:
lemma single_le_prod
  statement: [CommMonoid M] [Preorder M] [IsOrderedMonoid M]
  proof: by
  induction l
  · simp
  simp_rw [prod_cons, forall_mem_cons] at hl₁ ⊢
  constructor
  case cons.left => exact le_mul_of_one_le_right' (one_le_prod_of_one_le hl₁.2)
  case cons.right hd tl ih => exact fun x H => le_mul_of_one_le_of_le hl₁.1 (ih hl₁.right x H)

@[to_additive all_zero_of_le_zero_le

中文:
引理 single_le_prod
  结论: [交换幺半群 M] [预序 M] [是Ordered幺半群 M]
  证明: by
  induction l
  · simp
  simp_rw [prod_cons, forall_mem_cons] at hl₁ ⊢
  constructor
  case cons.left => exact le_mul_of_one_le_right' (one_le_prod_of_one_le hl₁.2)
  case cons.right hd tl ih => exact fun x H => le_mul_of_one_le_of_le hl₁.1 (ih hl₁.right x H)

@[to_additive all_zero_of_le_zero_le

Depends on / 依赖: cons.left, cons.right, forall_mem_cons, le_mul_of_one_le_of_le, le_mul_of_one_le_right, one_le_prod_of_one_le, prod_cons, simp_rw
-/
lemma single_le_prod [CommMonoid M] [Preorder M] [IsOrderedMonoid M]
    {l : List M} (hl₁ : forall x in l, (1 : M) <= x) :
    forall x in l, x <= l.prod := by
  induction l
  · simp
  simp_rw [prod_cons, forall_mem_cons] at hl₁ ⊢
  constructor
  case cons.left => exact le_mul_of_one_le_right' (one_le_prod_of_one_le hl₁.2)
  case cons.right hd tl ih => exact fun x H => le_mul_of_one_le_of_le hl₁.1 (ih hl₁.right x H)

@[to_additive all_zero_of_le_zero_le_of_sum_eq_zero]
/--
lemma `all_one_of_le_one_le_of_prod_eq_one` / 引理 `all_one_of_le_one_le_of_prod_eq_one`

English:
lemma all_one_of_le_one_le_of_prod_eq_one
  statement: [CommMonoid M] [PartialOrder M] [IsOrderedMonoid M]
  proof: _root_.le_antisymm (hl₂ ▸ single_le_prod hl₁ _ hx) (hl₁ x hx)

中文:
引理 all_one_of_le_one_le_of_prod_eq_one
  结论: [交换幺半群 M] [偏序 M] [是Ordered幺半群 M]
  证明: _root_.le_antisymm (hl₂ ▸ single_le_prod hl₁ _ hx) (hl₁ x hx)

Depends on / 依赖: _root_, _root_.le_antisymm, le_antisymm, single_le_prod
-/
lemma all_one_of_le_one_le_of_prod_eq_one [CommMonoid M] [PartialOrder M] [IsOrderedMonoid M]
    {l : List M} (hl₁ : forall x in l, (1 : M) <= x) (hl₂ : l.prod = 1) {x : M} (hx : x in l) : x = 1 :=
  _root_.le_antisymm (hl₂ ▸ single_le_prod hl₁ _ hx) (hl₁ x hx)

/--
lemma `prod_eq_one_iff` / 引理 `prod_eq_one_iff`

English:
lemma prod_eq_one_iff
  statement: [CommMonoid M] [PartialOrder M] [IsOrderedMonoid M]
  proof: ⟨all_one_of_le_one_le_of_prod_eq_one fun _ _ => one_le, fun h => by
    rw [List.eq_replicate_iff.2 ⟨_]; rw [h⟩]; rw [prod_replicate]; rw [one_pow]
    · exact (length l)
    · rfl⟩

中文:
引理 prod_eq_one_iff
  结论: [交换幺半群 M] [偏序 M] [是Ordered幺半群 M]
  证明: ⟨all_one_of_le_one_le_of_prod_eq_one fun _ _ => one_le, fun h => by
    rw [List.eq_replicate_iff.2 ⟨_]; rw [h⟩]; rw [prod_replicate]; rw [one_pow]
    · exact (length l)
    · rfl⟩
-/
@[to_additive] lemma prod_eq_one_iff [CommMonoid M] [PartialOrder M] [IsOrderedMonoid M]
     [CanonicallyOrderedMul M] {l : List M} : l.prod = 1 ↔ forall x in l, x = (1 : M) :=
  ⟨all_one_of_le_one_le_of_prod_eq_one fun _ _ => one_le, fun h => by
    rw [List.eq_replicate_iff.2 ⟨_]; rw [h⟩]; rw [prod_replicate]; rw [one_pow]
    · exact (length l)
    · rfl⟩

section ProdSum

variable {α β : Type*} [Monoid α] [AddMonoid β] [Preorder β] [AddLeftMono β]
  (l : List α) (f : α -> β)

/--
theorem `apply_prod_le_sum_map` / 定理 `apply_prod_le_sum_map`

English:
theorem apply_prod_le_sum_map
  given: (h_one : f 1 <= 0) (h_mul : forall (a b : α), f (a * b) <= f a + f b)
  proof: by
  induction l with
  | nil => simp [h_one]
  | cons hd tl IH => grw [prod_cons, h_mul, IH]; simp

中文:
定理 apply_prod_le_sum_map
  条件: (h_one : f 1 <= 0) (h_mul : 对任意 (a b : α), f (a * b) <= f a + f b)
  证明: by
  induction l with
  | nil => simp [h_one]
  | cons hd tl IH => grw [prod_cons, h_mul, IH]; simp

Depends on / 依赖: h_mul, h_one, prod_cons
-/
theorem apply_prod_le_sum_map (h_one : f 1 <= 0) (h_mul : forall (a b : α), f (a * b) <= f a + f b) :
    f l.prod <= (l.map f).sum := by
  induction l with
  | nil => simp [h_one]
  | cons hd tl IH => grw [prod_cons, h_mul, IH]; simp

/--
theorem `sum_map_le_apply_prod` / 定理 `sum_map_le_apply_prod`

English:
theorem sum_map_le_apply_prod
  given: (h_one : 0 <= f 1) (h_mul : forall (a b : α), f a + f b <= f (a * b))
  proof: apply_prod_le_sum_map (β := βᵒᵈ) l f h_one h_mul

中文:
定理 sum_map_le_apply_prod
  条件: (h_one : 0 <= f 1) (h_mul : 对任意 (a b : α), f a + f b <= f (a * b))
  证明: apply_prod_le_sum_map (β := βᵒᵈ) l f h_one h_mul

Depends on / 依赖: apply_prod_le_sum_map, h_mul, h_one
-/
theorem sum_map_le_apply_prod (h_one : 0 <= f 1) (h_mul : forall (a b : α), f a + f b <= f (a * b)) :
    (l.map f).sum <= f l.prod :=
  apply_prod_le_sum_map (β := βᵒᵈ) l f h_one h_mul

end ProdSum

end List
