/-
Copyright (c) 2025 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Fabrizio Barroero
-/
module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Order.Hom.Basic
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Nonarchimedean functions

A function `f : α → R` is nonarchimedean if it satisfies the strong triangle inequality
`f (a + b) ≤ max (f a) (f b)` for all `a b : α`. This file proves basic properties of
nonarchimedean functions.
-/

public section

/- TODO: Remove the Funlike hypothesis on these statements and turn them all into the form
  {f : α → R} + properties on f. -/

namespace IsNonarchimedean

variable {R : Type*} [Semiring R] [LinearOrder R] {a b : R} {m n : Nat}

/--
theorem `add_le` / 定理 `add_le`

English:
theorem add_le
  statement: [IsStrictOrderedRing R] {α : Type*} [Add α] {f : α -> R} (hf : forall x : α, 0 <= f x)
  proof: by
  apply le_trans (hna _ _)
  rw [max_le_iff]; rw [le_add_iff_nonneg_right]; rw [le_add_iff_nonneg_left]
  exact ⟨hf _, hf _⟩

中文:
定理 add_le
  结论: [是StrictOrdered环 R] {α : 类型} [加法 α] {f : α -> R} (hf : 对任意 x : α, 0 <= f x)
  证明: by
  apply le_trans (hna _ _)
  rw [max_le_iff]; rw [le_add_iff_nonneg_right]; rw [le_add_iff_nonneg_left]
  exact ⟨hf _, hf _⟩

Depends on / 依赖: le_add_iff_nonneg_left, le_add_iff_nonneg_right, le_trans, max_le_iff
-/
theorem add_le [IsStrictOrderedRing R] {α : Type*} [Add α] {f : α -> R} (hf : forall x : α, 0 <= f x)
    (hna : IsNonarchimedean f) {a b : α} : f (a + b) <= f a + f b := by
  apply le_trans (hna _ _)
  rw [max_le_iff]; rw [le_add_iff_nonneg_right]; rw [le_add_iff_nonneg_left]
  exact ⟨hf _, hf _⟩

/--
theorem `nsmul_le` / 定理 `nsmul_le`

English:
theorem nsmul_le
  statement: {F α : Type*} [AddMonoid α] [FunLike F α R] [ZeroHomClass F α R]
  proof: by
  induction n with
  | zero => simp
  | succ n _ =>
    rw [add_nsmul]
apply le_trans hna (n • a) (1 • a)
    simpa

中文:
定理 nsmul_le
  结论: {F α : 类型} [加法幺半群 α] [函数状 F α R] [保零态射类 F α R]
  证明: by
  induction n with
  | zero => simp
  | succ n _ =>
    rw [add_nsmul]
apply le_trans hna (n • a) (1 • a)
    simpa

Depends on / 依赖: add_nsmul, le_trans
-/
theorem nsmul_le {F α : Type*} [AddMonoid α] [FunLike F α R] [ZeroHomClass F α R]
    [NonnegHomClass F α R] {f : F} (hna : IsNonarchimedean f) {n : Nat} {a : α} :
    f (n • a) <= f a := by
  induction n with
  | zero => simp
  | succ n _ =>
    rw [add_nsmul]
apply le_trans hna (n • a) (1 • a)
    simpa

/--
theorem `nmul_le` / 定理 `nmul_le`

English:
theorem nmul_le
  statement: {F α : Type*} [NonAssocSemiring α] [FunLike F α R] [ZeroHomClass F α R]
  proof: by
  rw [← nsmul_eq_mul]
  exact nsmul_le hna

中文:
定理 nmul_le
  结论: {F α : 类型} [非结合半环 α] [函数状 F α R] [保零态射类 F α R]
  证明: by
  rw [← nsmul_eq_mul]
  exact nsmul_le hna

Depends on / 依赖: nsmul_eq_mul, nsmul_le
-/
theorem nmul_le {F α : Type*} [NonAssocSemiring α] [FunLike F α R] [ZeroHomClass F α R]
    [NonnegHomClass F α R] {f : F} (hna : IsNonarchimedean f) {n : Nat} {a : α} :
    f (n * a) <= f a := by
  rw [← nsmul_eq_mul]
  exact nsmul_le hna

/--
lemma `apply_natCast_le_one` / 引理 `apply_natCast_le_one`

English:
lemma apply_natCast_le_one
  statement: {F α : Type*} [AddMonoidWithOne α] [FunLike F α R]
  proof: by
  rw [← nsmul_one n]; rw [← map_one f]
  exact nsmul_le hna

@[deprecated (since := "2026-04-27")]
alias apply_natCast_le_one_of_isNonarchimedean := apply_natCast_le_one

中文:
引理 apply_natCast_le_one
  结论: {F α : 类型} [加法带幺幺半群 α] [函数状 F α R]
  证明: by
  rw [← nsmul_one n]; rw [← map_one f]
  exact nsmul_le hna

@[deprecated (since := "2026-04-27")]
alias apply_natCast_le_one_of_isNonarchimedean := apply_natCast_le_one

Depends on / 依赖: map_one, nsmul_le, nsmul_one
-/
lemma apply_natCast_le_one {F α : Type*} [AddMonoidWithOne α] [FunLike F α R]
    [ZeroHomClass F α R] [NonnegHomClass F α R] [OneHomClass F α R] {f : F}
    (hna : IsNonarchimedean f) {n : Nat} : f n <= 1 := by
  rw [← nsmul_one n]; rw [← map_one f]
  exact nsmul_le hna

@[deprecated (since := "2026-04-27")]
alias apply_natCast_le_one_of_isNonarchimedean := apply_natCast_le_one

/--
theorem `apply_intCast_le_one` / 定理 `apply_intCast_le_one`

English:
theorem apply_intCast_le_one
  statement: [IsStrictOrderedRing R]
  proof: by
  obtain ⟨a, rfl | rfl⟩ := Int.eq_nat_or_neg n <;>
  simp [apply_natCast_le_one hna]

@[deprecated (since := "2026-04-27")]
alias apply_intCast_le_one_of_isNonarchimedean := apply_intCast_le_one

中文:
定理 apply_intCast_le_one
  结论: [是StrictOrdered环 R]
  证明: by
  obtain ⟨a, rfl | rfl⟩ := Int.eq_nat_or_neg n <;>
  simp [apply_natCast_le_one hna]

@[deprecated (since := "2026-04-27")]
alias apply_intCast_le_one_of_isNonarchimedean := apply_intCast_le_one

Depends on / 依赖: Int.eq_nat_or_neg, apply_natCast_le_one, eq_nat_or_neg
-/
theorem apply_intCast_le_one [IsStrictOrderedRing R]
    {F α : Type*} [AddGroupWithOne α] [FunLike F α R]
    [AddGroupSeminormClass F α R] [OneHomClass F α R] {f : F}
    (hna : IsNonarchimedean f) {n : Int} : f n <= 1 := by
  obtain ⟨a, rfl | rfl⟩ := Int.eq_nat_or_neg n <;>
  simp [apply_natCast_le_one hna]

@[deprecated (since := "2026-04-27")]
alias apply_intCast_le_one_of_isNonarchimedean := apply_intCast_le_one

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
lemma `add_eq_right_of_lt` / 引理 `add_eq_right_of_lt`

English:
lemma add_eq_right_of_lt
  statement: {F α : Type*} [AddGroup α] [FunLike F α R]
  proof: by
  by_contra! h
  have h1 : f (x + y) <= f y := (hna x y).trans_eq (max_eq_right_of_lt h_lt)
  apply lt_irrefl (f y)
  calc
    f y = f (-x + (x + y)) := by simp
    _ <= max (f (-x)) (f (x + y)) := hna (-x) (x + y)
    _ < max (f y) (f y) := by
      rw [max_self]; rw [map_neg_eq_map]
exact max_l

中文:
引理 add_eq_right_of_lt
  结论: {F α : 类型} [加法群 α] [函数状 F α R]
  证明: by
  by_contra! h
  have h1 : f (x + y) <= f y := (hna x y).trans_eq (max_eq_right_of_lt h_lt)
  apply lt_irrefl (f y)
  calc
    f y = f (-x + (x + y)) := by simp
    _ <= max (f (-x)) (f (x + y)) := hna (-x) (x + y)
    _ < max (f y) (f y) := by
      rw [max_self]; rw [map_neg_eq_map]
exact max_l

Depends on / 依赖: h_lt, lt_irrefl, lt_of_le_of_ne, map_neg_eq_map, max_eq_right_of_lt, max_lt, max_self, trans_eq
-/
lemma add_eq_right_of_lt {F α : Type*} [AddGroup α] [FunLike F α R]
    [AddGroupSeminormClass F α R] {f : F} (hna : IsNonarchimedean f) {x y : α}
    (h_lt : f x < f y) : f (x + y) = f y := by
  by_contra! h
  have h1 : f (x + y) <= f y := (hna x y).trans_eq (max_eq_right_of_lt h_lt)
  apply lt_irrefl (f y)
  calc
    f y = f (-x + (x + y)) := by simp
    _ <= max (f (-x)) (f (x + y)) := hna (-x) (x + y)
    _ < max (f y) (f y) := by
      rw [max_self]; rw [map_neg_eq_map]
exact max_lt h_lt lt_of_le_of_ne h1 h
    _ = f y := max_self (f y)

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
lemma `add_eq_left_of_lt` / 引理 `add_eq_left_of_lt`

English:
lemma add_eq_left_of_lt
  statement: {F α : Type*} [AddGroup α] [FunLike F α R]
  proof: by
  by_contra! h
  have h1 : f (x + y) <= f x := (hna x y).trans_eq (max_eq_left_of_lt h_lt)
  apply lt_irrefl (f x)
  calc
    f x = f (x + y + -y) := by simp
    _ <= max (f (x + y)) (f (-y)) := hna (x + y) (-y)
    _ < max (f x) (f x) := by
      rw [max_self]; rw [map_neg_eq_map]
      apply ma

中文:
引理 add_eq_left_of_lt
  结论: {F α : 类型} [加法群 α] [函数状 F α R]
  证明: by
  by_contra! h
  have h1 : f (x + y) <= f x := (hna x y).trans_eq (max_eq_left_of_lt h_lt)
  apply lt_irrefl (f x)
  calc
    f x = f (x + y + -y) := by simp
    _ <= max (f (x + y)) (f (-y)) := hna (x + y) (-y)
    _ < max (f x) (f x) := by
      rw [max_self]; rw [map_neg_eq_map]
      apply ma

Depends on / 依赖: h_lt, lt_irrefl, lt_of_le_of_ne, map_neg_eq_map, max_eq_left_of_lt, max_lt, max_self, trans_eq
-/
lemma add_eq_left_of_lt {F α : Type*} [AddGroup α] [FunLike F α R]
    [AddGroupSeminormClass F α R] {f : F} (hna : IsNonarchimedean f) {x y : α}
    (h_lt : f y < f x) : f (x + y) = f x := by
  by_contra! h
  have h1 : f (x + y) <= f x := (hna x y).trans_eq (max_eq_left_of_lt h_lt)
  apply lt_irrefl (f x)
  calc
    f x = f (x + y + -y) := by simp
    _ <= max (f (x + y)) (f (-y)) := hna (x + y) (-y)
    _ < max (f x) (f x) := by
      rw [max_self]; rw [map_neg_eq_map]
      apply max_lt (lt_of_le_of_ne h1 h) h_lt
    _ = f x := max_self (f x)

/--
theorem `add_eq_max_of_ne` / 定理 `add_eq_max_of_ne`

English:
theorem add_eq_max_of_ne
  statement: {F α : Type*} [AddGroup α] [FunLike F α R]
  proof: by
  rcases hne.lt_or_gt with h_lt | h_lt
  · rw [add_eq_right_of_lt hna h_lt]
    exact (max_eq_right_of_lt h_lt).symm
  · rw [add_eq_left_of_lt hna h_lt]
    exact (max_eq_left_of_lt h_lt).symm

中文:
定理 add_eq_max_of_ne
  结论: {F α : 类型} [加法群 α] [函数状 F α R]
  证明: by
  rcases hne.lt_or_gt with h_lt | h_lt
  · rw [add_eq_right_of_lt hna h_lt]
    exact (max_eq_right_of_lt h_lt).symm
  · rw [add_eq_left_of_lt hna h_lt]
    exact (max_eq_left_of_lt h_lt).symm

Depends on / 依赖: add_eq_left_of_lt, add_eq_right_of_lt, h_lt, hne.lt_or_gt, lt_or_gt, max_eq_left_of_lt, max_eq_right_of_lt
-/
theorem add_eq_max_of_ne {F α : Type*} [AddGroup α] [FunLike F α R]
    [AddGroupSeminormClass F α R] {f : F} (hna : IsNonarchimedean f) {x y : α} (hne : f x != f y) :
    f (x + y) = max (f x) (f y) := by
  rcases hne.lt_or_gt with h_lt | h_lt
  · rw [add_eq_right_of_lt hna h_lt]
    exact (max_eq_right_of_lt h_lt).symm
  · rw [add_eq_left_of_lt hna h_lt]
    exact (max_eq_left_of_lt h_lt).symm


/--
lemma `add_eq_max_of_ne'` / 引理 `add_eq_max_of_ne'`

English:
lemma add_eq_max_of_ne'
  statement: {α S : Type*} [LinearOrder S] [AddCommGroup α]
  proof: by
  wlog hab : f a > f b generalizing a b with H
  · simpa [add_comm, max_comm] using (H hne.symm ((not_lt.mp hab).lt_of_ne hne))
  apply le_antisymm (fna a b)
  rcases le_max_iff.mp (fna (a + b) (-b)) with h | h
  · simpa [max_eq_left (le_of_lt hab)] using h
  · exact absurd h (not_le.mpr (by simp

中文:
引理 add_eq_max_of_ne'
  结论: {α S : 类型} [线性序 S] [加法交换群 α]
  证明: by
  wlog hab : f a > f b generalizing a b with H
  · simpa [add_comm, max_comm] using (H hne.symm ((not_lt.mp hab).lt_of_ne hne))
  apply le_antisymm (fna a b)
  rcases le_max_iff.mp (fna (a + b) (-b)) with h | h
  · simpa [max_eq_left (le_of_lt hab)] using h
  · exact absurd h (not_le.mpr (by simp

Depends on / 依赖: absurd, add_comm, generalizing, hne.symm, le_antisymm, le_max_iff, le_max_iff.mp, le_of_lt, lt_of_ne, max_comm, max_eq_left, not_le, not_le.mpr, not_lt, not_lt.mp
-/
lemma add_eq_max_of_ne' {α S : Type*} [LinearOrder S] [AddCommGroup α]
    (f : α -> S) (fna : IsNonarchimedean f) (Neg : forall a, f a = f (-a)) {a b : α}
    (hne : f a != f b) : f (a + b) = max (f a) (f b) := by
  wlog hab : f a > f b generalizing a b with H
  · simpa [add_comm, max_comm] using (H hne.symm ((not_lt.mp hab).lt_of_ne hne))
  apply le_antisymm (fna a b)
  rcases le_max_iff.mp (fna (a + b) (-b)) with h | h
  · simpa [max_eq_left (le_of_lt hab)] using h
  · exact absurd h (not_le.mpr (by simpa [Neg b] using hab))

omit [Semiring R] in
open Finset in
/--
lemma `apply_sum_le_sup` / 引理 `apply_sum_le_sup`

English:
lemma apply_sum_le_sup
  statement: {α β : Type*} [AddCommMonoid α] {f : α -> R}
  proof: by
  induction hnonempty using Nonempty.cons_induction with
  | singleton i => simp
  | cons i s _ hs hind =>
    simp only [sum_cons, le_sup'_iff, mem_cons, exists_eq_or_imp]
    rw [← le_sup'_iff hs]
rcases le_max_iff.mp nonarch (l i) (∑ i in s, l i) with h₁ | h₂
    · exact .inl h₁
· exact .inr l

中文:
引理 apply_sum_le_sup
  结论: {α β : 类型} [加法交换幺半群 α] {f : α -> R}
  证明: by
  induction hnonempty using Nonempty.cons_induction with
  | singleton i => simp
  | cons i s _ hs hind =>
    simp only [sum_cons, le_sup'_iff, mem_cons, exists_eq_or_imp]
    rw [← le_sup'_iff hs]
rcases le_max_iff.mp nonarch (l i) (∑ i in s, l i) with h₁ | h₂
    · exact .inl h₁
· exact .inr l

Depends on / 依赖: Nonempty, Nonempty.cons_induction, _iff, cons_induction, exists_eq_or_imp, hnonempty, le_max_iff, le_max_iff.mp, le_sup, le_trans, mem_cons, nonarch, singleton, sum_cons
-/
lemma apply_sum_le_sup {α β : Type*} [AddCommMonoid α] {f : α -> R}
    (nonarch : IsNonarchimedean f) {s : Finset β} (hnonempty : s.Nonempty) {l : β -> α} :
    f (∑ i in s, l i) <= s.sup' hnonempty fun i => f (l i) := by
  induction hnonempty using Nonempty.cons_induction with
  | singleton i => simp
  | cons i s _ hs hind =>
    simp only [sum_cons, le_sup'_iff, mem_cons, exists_eq_or_imp]
    rw [← le_sup'_iff hs]
rcases le_max_iff.mp nonarch (l i) (∑ i in s, l i) with h₁ | h₂
    · exact .inl h₁
· exact .inr le_trans h₂ hind

@[deprecated (since := "2026-04-27")]
alias apply_sum_le_sup_of_isNonarchimedean := apply_sum_le_sup

omit [Semiring R] in
/--
theorem `multiset_image_add_of_nonempty` / 定理 `multiset_image_add_of_nonempty`

English:
theorem multiset_image_add_of_nonempty
  statement: {α β : Type*} [AddCommMonoid α] [Nonempty β] {f : α -> R}
  proof: by
  induction s using Multiset.induction_on with
  | empty => contradiction
  | cons a s h =>
    simp only [Multiset.mem_cons, Multiset.map_cons, Multiset.sum_cons, exists_eq_or_imp]
    by_cases h1 : s = 0
    · simp [h1]
    · obtain ⟨w, h2, h3⟩ := h h1
rcases le_max_iff.mp hna (g a) (Multiset.m

中文:
定理 multiset_image_add_of_nonempty
  结论: {α β : 类型} [加法交换幺半群 α] [非空 β] {f : α -> R}
  证明: by
  induction s using Multiset.induction_on with
  | empty => contradiction
  | cons a s h =>
    simp only [Multiset.mem_cons, Multiset.map_cons, Multiset.sum_cons, exists_eq_or_imp]
    by_cases h1 : s = 0
    · simp [h1]
    · obtain ⟨w, h2, h3⟩ := h h1
rcases le_max_iff.mp hna (g a) (Multiset.m

Depends on / 依赖: Multiset, Multiset.induction_on, Multiset.map, Multiset.map_cons, Multiset.mem_cons, Multiset.sum_cons, exists_eq_or_imp, induction_on, le_max_iff, le_max_iff.mp, le_trans, map_cons, mem_cons, sum_cons
-/
theorem multiset_image_add_of_nonempty {α β : Type*} [AddCommMonoid α] [Nonempty β] {f : α -> R}
    (hna : IsNonarchimedean f) (g : β -> α) {s : Multiset β} (hs : s != 0) :
    exists b : β, (b in s) ∧ f (Multiset.map g s).sum <= f (g b) := by
  induction s using Multiset.induction_on with
  | empty => contradiction
  | cons a s h =>
    simp only [Multiset.mem_cons, Multiset.map_cons, Multiset.sum_cons, exists_eq_or_imp]
    by_cases h1 : s = 0
    · simp [h1]
    · obtain ⟨w, h2, h3⟩ := h h1
rcases le_max_iff.mp hna (g a) (Multiset.map g s).sum with h4 | h4
      · exact .inl h4
      · exact .inr ⟨w, h2, le_trans h4 h3⟩

omit [Semiring R] in
/--
theorem `finset_image_add_of_nonempty` / 定理 `finset_image_add_of_nonempty`

English:
theorem finset_image_add_of_nonempty
  statement: {α β : Type*} [AddCommMonoid α] {f : α -> R}
  proof: by
  simpa [Finset.le_sup'_iff] using IsNonarchimedean.apply_sum_le_sup hna ht

中文:
定理 finset_image_add_of_nonempty
  结论: {α β : 类型} [加法交换幺半群 α] {f : α -> R}
  证明: by
  simpa [Finset.le_sup'_iff] using IsNonarchimedean.apply_sum_le_sup hna ht

Depends on / 依赖: Finset, Finset.le_sup, IsNonarchimedean, IsNonarchimedean.apply_sum_le_sup, _iff, apply_sum_le_sup, le_sup
-/
theorem finset_image_add_of_nonempty {α β : Type*} [AddCommMonoid α] {f : α -> R}
    (hna : IsNonarchimedean f) (g : β -> α) {t : Finset β} (ht : t.Nonempty) :
    exists b in t, f (t.sum g) <= f (g b) := by
  simpa [Finset.le_sup'_iff] using IsNonarchimedean.apply_sum_le_sup hna ht

/--
theorem `multiset_image_add` / 定理 `multiset_image_add`

English:
theorem multiset_image_add
  statement: {F α β : Type*} [AddCommMonoid α] [FunLike F α R] [ZeroHomClass F α R]
  proof: by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s h =>
    obtain ⟨b, hb1, hb2⟩ := multiset_image_add_of_nonempty (s := a ::ₘ s)
      hna g Multiset.cons_ne_zero
    exact ⟨b, fun _ => hb1, hb2⟩

中文:
定理 multiset_image_add
  结论: {F α β : 类型} [加法交换幺半群 α] [函数状 F α R] [保零态射类 F α R]
  证明: by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s h =>
    obtain ⟨b, hb1, hb2⟩ := multiset_image_add_of_nonempty (s := a ::ₘ s)
      hna g Multiset.cons_ne_zero
    exact ⟨b, fun _ => hb1, hb2⟩

Depends on / 依赖: Multiset, Multiset.cons_ne_zero, Multiset.induction_on, cons_ne_zero, induction_on, multiset_image_add_of_nonempty
-/
theorem multiset_image_add {F α β : Type*} [AddCommMonoid α] [FunLike F α R] [ZeroHomClass F α R]
    [NonnegHomClass F α R] [Nonempty β] {f : F} (hna : IsNonarchimedean f) (g : β -> α)
    (s : Multiset β) : exists b : β, (s != 0 -> b in s) ∧ f (Multiset.map g s).sum <= f (g b) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s h =>
    obtain ⟨b, hb1, hb2⟩ := multiset_image_add_of_nonempty (s := a ::ₘ s)
      hna g Multiset.cons_ne_zero
    exact ⟨b, fun _ => hb1, hb2⟩

/--
lemma `finset_image_add` / 引理 `finset_image_add`

English:
lemma finset_image_add
  statement: {α β : Type*} [AddCommMonoid α] [Nonempty β] {f : α -> R} (f_zero : f 0 = 0)
  proof: by
  rcases t.eq_empty_or_nonempty with rfl | ht
  · simp [f_zero, f_nonneg]
· exact (fun ⟨i, h, h'⟩ => ⟨i, fun _ => h, h'⟩)
      IsNonarchimedean.finset_image_add_of_nonempty hna g ht

中文:
引理 finset_image_add
  结论: {α β : 类型} [加法交换幺半群 α] [非空 β] {f : α -> R} (f_zero : f 0 = 0)
  证明: by
  rcases t.eq_empty_or_nonempty with rfl | ht
  · simp [f_zero, f_nonneg]
· exact (fun ⟨i, h, h'⟩ => ⟨i, fun _ => h, h'⟩)
      IsNonarchimedean.finset_image_add_of_nonempty hna g ht

Depends on / 依赖: IsNonarchimedean, IsNonarchimedean.finset_image_add_of_nonempty, eq_empty_or_nonempty, f_nonneg, f_zero, finset_image_add_of_nonempty, t.eq_empty_or_nonempty
-/
lemma finset_image_add {α β : Type*} [AddCommMonoid α] [Nonempty β] {f : α -> R} (f_zero : f 0 = 0)
    (f_nonneg : forall x, 0 <= f x) (hna : IsNonarchimedean f) (g : β -> α) (t : Finset β) :
    exists i, (t.Nonempty -> i in t) ∧ f (t.sum g) <= f (g i) := by
  rcases t.eq_empty_or_nonempty with rfl | ht
  · simp [f_zero, f_nonneg]
· exact (fun ⟨i, h, h'⟩ => ⟨i, fun _ => h, h'⟩)
      IsNonarchimedean.finset_image_add_of_nonempty hna g ht

open Multiset in
/--
theorem `multiset_powerset_image_add` / 定理 `multiset_powerset_image_add`

English:
theorem multiset_powerset_image_add
  statement: [IsStrictOrderedRing R]
  proof: by
  set g := fun t : Multiset α => t.prod
  obtain ⟨b, hb_in, hb_le⟩ := hf_na.multiset_image_add g (powersetCard (card s - m) s)
  have hb : b <= s ∧ card b = card s - m := by
    rw [← mem_powersetCard]
    exact hb_in (card_pos.mp
      (card_powersetCard (s.card - m) s ▸ Nat.choose_pos ((card s)

中文:
定理 multiset_powerset_image_add
  结论: [是StrictOrdered环 R]
  证明: by
  set g := fun t : Multiset α => t.prod
  obtain ⟨b, hb_in, hb_le⟩ := hf_na.multiset_image_add g (powersetCard (card s - m) s)
  have hb : b <= s ∧ card b = card s - m := by
    rw [← mem_powersetCard]
    exact hb_in (card_pos.mp
      (card_powersetCard (s.card - m) s ▸ Nat.choose_pos ((card s)

Depends on / 依赖: Multiset, Nat.choose_pos, card_pos, card_pos.mp, card_powersetCard, choose_pos, hb.left, hb_in, hb_le, hf_na, hf_na.multiset_image_add, mem_of_le, mem_powersetCard, multiset_image_add, powersetCard, s.card, sub_le, t.prod
-/
theorem multiset_powerset_image_add [IsStrictOrderedRing R]
    {F α : Type*} [CommRing α] [FunLike F α R]
    [AddGroupSeminormClass F α R] {f : F} (hf_na : IsNonarchimedean f) (s : Multiset α) (m : Nat) :
    exists t : Multiset α, card t = card s - m ∧ (forall x : α, x in t -> x in s) ∧
      f (map prod (powersetCard (card s - m) s)).sum <= f t.prod := by
  set g := fun t : Multiset α => t.prod
  obtain ⟨b, hb_in, hb_le⟩ := hf_na.multiset_image_add g (powersetCard (card s - m) s)
  have hb : b <= s ∧ card b = card s - m := by
    rw [← mem_powersetCard]
    exact hb_in (card_pos.mp
      (card_powersetCard (s.card - m) s ▸ Nat.choose_pos ((card s).sub_le m)))
  exact ⟨b, hb.2, fun x hx => mem_of_le hb.left hx, hb_le⟩

open Finset in
/--
theorem `finset_powerset_image_add` / 定理 `finset_powerset_image_add`

English:
theorem finset_powerset_image_add
  statement: [IsStrictOrderedRing R]
  proof: by
  set g := fun t : Finset β => t.prod fun i : β => - b i
  obtain ⟨b, hb_in, hb⟩ := hf_na.finset_image_add (by grind) (apply_nonneg f)
    g (powersetCard (s.card - m) s)
  exact ⟨⟨b, hb_in (powersetCard_nonempty.mpr (Nat.sub_le s.card m))⟩, hb⟩

omit [Semiring R] in

中文:
定理 finset_powerset_image_add
  结论: [是StrictOrdered环 R]
  证明: by
  set g := fun t : Finset β => t.prod fun i : β => - b i
  obtain ⟨b, hb_in, hb⟩ := hf_na.finset_image_add (by grind) (apply_nonneg f)
    g (powersetCard (s.card - m) s)
  exact ⟨⟨b, hb_in (powersetCard_nonempty.mpr (Nat.sub_le s.card m))⟩, hb⟩

omit [Semiring R] in

Depends on / 依赖: Finset, Nat.sub_le, apply_nonneg, finset_image_add, hb_in, hf_na, hf_na.finset_image_add, powersetCard, powersetCard_nonempty, powersetCard_nonempty.mpr, s.card, sub_le, t.prod
-/
theorem finset_powerset_image_add [IsStrictOrderedRing R]
    {F α β : Type*} [CommRing α] [FunLike F α R]
    [AddGroupSeminormClass F α R] {f : F} (hf_na : IsNonarchimedean f) (s : Finset β)
    (b : β -> α) (m : Nat) :
    exists u : powersetCard (s.card - m) s,
      f ((powersetCard (s.card - m) s).sum fun t : Finset β =>
        t.prod fun i : β => -b i) <= f (u.val.prod fun i : β => -b i) := by
  set g := fun t : Finset β => t.prod fun i : β => - b i
  obtain ⟨b, hb_in, hb⟩ := hf_na.finset_image_add (by grind) (apply_nonneg f)
    g (powersetCard (s.card - m) s)
  exact ⟨⟨b, hb_in (powersetCard_nonempty.mpr (Nat.sub_le s.card m))⟩, hb⟩

omit [Semiring R] in
/--
lemma `apply_sum_eq_of_lt` / 引理 `apply_sum_eq_of_lt`

English:
lemma apply_sum_eq_of_lt
  statement: {α β : Type*} [AddCommGroup α] {f : α -> R} (fna : IsNonarchimedean f)
  proof: by
  by_cases hcard : s.card = 1
  · grind [Finset.card_eq_one.mp hcard]
  · classical
    rw [← Finset.add_sum_erase _ _ hk]
    have hNonempty : (s.erase k).Nonempty :=
      Finset.Nontrivial.erase_nonempty (Finset.one_lt_card_iff_nontrivial.mp (by grind))
    have hrest_le := IsNonarchimedean.ap

中文:
引理 apply_sum_eq_of_lt
  结论: {α β : 类型} [加法交换群 α] {f : α -> R} (fna : IsNonarchimedean f)
  证明: by
  by_cases hcard : s.card = 1
  · grind [Finset.card_eq_one.mp hcard]
  · classical
    rw [← Finset.add_sum_erase _ _ hk]
    have hNonempty : (s.erase k).Nonempty :=
      Finset.Nontrivial.erase_nonempty (Finset.one_lt_card_iff_nontrivial.mp (by grind))
    have hrest_le := IsNonarchimedean.ap

Depends on / 依赖: Finset, Finset.Nontrivial.erase_nonempty, Finset.add_sum_erase, Finset.card_eq_one.mp, Finset.le_sup, Finset.mem_erase, Finset.one_lt_card_iff_nontrivial.mp, IsNonarchimedean, IsNonarchimedean.apply_sum_le_sup, Nonempty, Nontrivial, _iff, add_eq_max_of_ne, add_sum_erase, apply_sum_le_sup, card_eq_one, classical, erase_nonempty, f_neg, hNonempty
-/
lemma apply_sum_eq_of_lt {α β : Type*} [AddCommGroup α] {f : α -> R} (fna : IsNonarchimedean f)
    (f_neg : forall a, f a = f (-a)) {s : Finset β} {l : β -> α} {k : β} (hk : k in s)
    (hmax : forall j in s, j != k -> f (l j) < f (l k)) : f (∑ i in s, l i) = f (l k) := by
  by_cases hcard : s.card = 1
  · grind [Finset.card_eq_one.mp hcard]
  · classical
    rw [← Finset.add_sum_erase _ _ hk]
    have hNonempty : (s.erase k).Nonempty :=
      Finset.Nontrivial.erase_nonempty (Finset.one_lt_card_iff_nontrivial.mp (by grind))
    have hrest_le := IsNonarchimedean.apply_sum_le_sup fna hNonempty (l := l)
    simp only [Finset.le_sup'_iff, Finset.mem_erase, ne_eq] at hrest_le
    rw [add_eq_max_of_ne' f fna f_neg (by grind)]; rw [max_eq_left (le_of_lt (by grind))]

/--
theorem `add_pow_le` / 定理 `add_pow_le`

English:
theorem add_pow_le
  statement: {F α : Type*} [CommRing α] [FunLike F α R] [ZeroHomClass F α R]
  proof: by
  obtain ⟨m, hm_lt, hM⟩ := finset_image_add (by aesop) (by aesop) hna
    (fun m => a ^ m * b ^ (n - m) * ↑(n.choose m)) (Finset.range (n + 1))
  simp only [Finset.nonempty_range_iff, ne_eq, Nat.succ_ne_zero, not_false_iff, Finset.mem_range,
    forall_true_left] at hm_lt
  refine ⟨m, hm_lt, ?_⟩


中文:
定理 add_pow_le
  结论: {F α : 类型} [交换环 α] [函数状 F α R] [保零态射类 F α R]
  证明: by
  obtain ⟨m, hm_lt, hM⟩ := finset_image_add (by aesop) (by aesop) hna
    (fun m => a ^ m * b ^ (n - m) * ↑(n.choose m)) (Finset.range (n + 1))
  simp only [Finset.nonempty_range_iff, ne_eq, Nat.succ_ne_zero, not_false_iff, Finset.mem_range,
    forall_true_left] at hm_lt
  refine ⟨m, hm_lt, ?_⟩


Depends on / 依赖: Finset, Finset.mem_range, Finset.nonempty_range_iff, Finset.range, Nat.succ_ne_zero, add_pow, finset_image_add, forall_true_left, hm_lt, le_trans, map_mul_le_mul, mem_range, mul_comm, n.choose, ne_eq, nmul_le, nonempty_range_iff, not_false_iff, succ_ne_zero
-/
theorem add_pow_le {F α : Type*} [CommRing α] [FunLike F α R] [ZeroHomClass F α R]
    [NonnegHomClass F α R] [SubmultiplicativeHomClass F α R] {f : F} (hna : IsNonarchimedean f)
    (n : Nat) (a b : α) : exists m < n + 1, f ((a + b) ^ n) <= f (a ^ m) * f (b ^ (n - m)) := by
  obtain ⟨m, hm_lt, hM⟩ := finset_image_add (by aesop) (by aesop) hna
    (fun m => a ^ m * b ^ (n - m) * ↑(n.choose m)) (Finset.range (n + 1))
  simp only [Finset.nonempty_range_iff, ne_eq, Nat.succ_ne_zero, not_false_iff, Finset.mem_range,
    forall_true_left] at hm_lt
  refine ⟨m, hm_lt, ?_⟩
  simp only [← add_pow] at hM
  rw [mul_comm] at hM
  exact le_trans hM (le_trans (nmul_le hna) (map_mul_le_mul _ _ _))

end IsNonarchimedean
