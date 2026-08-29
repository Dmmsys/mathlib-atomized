/-
Copyright (c) 2021 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
public import Mathlib.Algebra.Order.BigOperators.Ring.List

/-!
# Big operators on a multiset in ordered rings

This file contains the results concerning the interaction of multiset big operators with ordered
rings.
-/

public section

open Multiset

@[simp]
/--
lemma `CanonicallyOrderedAdd.multiset_prod_pos` / 引理 `CanonicallyOrderedAdd.multiset_prod_pos`

English:
lemma CanonicallyOrderedAdd.multiset_prod_pos
  statement: {R : Type*}
  proof: by
  rcases m with ⟨l⟩
  rw [Multiset.quot_mk_to_coe'']; rw [Multiset.prod_coe]
  exact CanonicallyOrderedAdd.list_prod_pos

中文:
引理 CanonicallyOrderedAdd.multiset_prod_pos
  结论: {R : 类型}
  证明: by
  rcases m with ⟨l⟩
  rw [Multiset.quot_mk_to_coe'']; rw [Multiset.prod_coe]
  exact CanonicallyOrderedAdd.list_prod_pos

Depends on / 依赖: CanonicallyOrderedAdd, CanonicallyOrderedAdd.list_prod_pos, Multiset, Multiset.prod_coe, Multiset.quot_mk_to_coe, list_prod_pos, prod_coe, quot_mk_to_coe
-/
lemma CanonicallyOrderedAdd.multiset_prod_pos {R : Type*}
    [CommSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R] [NoZeroDivisors R] [Nontrivial R]
    {m : Multiset R} : 0 < m.prod ↔ forall x in m, 0 < x := by
  rcases m with ⟨l⟩
  rw [Multiset.quot_mk_to_coe'']; rw [Multiset.prod_coe]
  exact CanonicallyOrderedAdd.list_prod_pos

section OrderedCommSemiring

variable {α β : Type*} [CommMonoid α] [CommMonoidWithZero β] [PartialOrder β] [PosMulMono β]

/--
theorem `Multiset.le_prod_of_submultiplicative_on_pred_of_nonneg` / 定理 `Multiset.le_prod_of_submultiplicative_on_pred_of_nonneg`

English:
theorem Multiset.le_prod_of_submultiplicative_on_pred_of_nonneg
  statement: (f : α -> β) (p : α -> Prop)
  proof: by
  revert s
  refine Multiset.induction (by simp [h_one]) ?_
  intro a s hs hpsa
  by_cases hs0 : s = ∅
  · simp [hs0]
  · have hps : forall x, x in s -> p x := fun x hx => hpsa x (mem_cons_of_mem hx)
    have hp_prod : p s.prod := prod_induction_nonempty p hp_mul hs0 hps
    rw [prod_cons]; rw [m

中文:
定理 Multiset.le_prod_of_submultiplicative_on_pred_of_nonneg
  结论: (f : α -> β) (p : α -> 命题)
  证明: by
  revert s
  refine Multiset.induction (by simp [h_one]) ?_
  intro a s hs hpsa
  by_cases hs0 : s = ∅
  · simp [hs0]
  · have hps : forall x, x in s -> p x := fun x hx => hpsa x (mem_cons_of_mem hx)
    have hp_prod : p s.prod := prod_induction_nonempty p hp_mul hs0 hps
    rw [prod_cons]; rw [m

Depends on / 依赖: Multiset, Multiset.induction, exacts, h_mul, h_one, hp_mul, hp_prod, map_cons, mem_cons_of_mem, mem_cons_self, prod_cons, prod_induction_nonempty, revert, s.prod
-/
theorem Multiset.le_prod_of_submultiplicative_on_pred_of_nonneg (f : α -> β) (p : α -> Prop)
    (h0 : forall a, 0 <= f a) (h_one : f 1 <= 1) (h_mul : forall a b, p a -> p b -> f (a * b) <= f a * f b)
    (hp_mul : forall a b, p a -> p b -> p (a * b)) (s : Multiset α) (hps : forall a, a in s -> p a) :
    f s.prod <= (s.map f).prod := by
  revert s
  refine Multiset.induction (by simp [h_one]) ?_
  intro a s hs hpsa
  by_cases hs0 : s = ∅
  · simp [hs0]
  · have hps : forall x, x in s -> p x := fun x hx => hpsa x (mem_cons_of_mem hx)
    have hp_prod : p s.prod := prod_induction_nonempty p hp_mul hs0 hps
    rw [prod_cons]; rw [map_cons]; rw [prod_cons]
    exact (h_mul a s.prod (hpsa a (mem_cons_self a s)) hp_prod).trans
      (by gcongr; exacts [h0 _, hs hps])

/--
theorem `Multiset.le_prod_of_submultiplicative_of_nonneg` / 定理 `Multiset.le_prod_of_submultiplicative_of_nonneg`

English:
theorem Multiset.le_prod_of_submultiplicative_of_nonneg
  statement: (f : α -> β) (h0 : forall a, 0 <= f a)
  proof: le_prod_of_submultiplicative_on_pred_of_nonneg f (fun _ => True) h0 h_one
    (fun x y _ _ => h_mul x y) (by simp) s (by simp)

omit [CommMonoid α] in

中文:
定理 Multiset.le_prod_of_submultiplicative_of_nonneg
  结论: (f : α -> β) (h0 : 对任意 a, 0 <= f a)
  证明: le_prod_of_submultiplicative_on_pred_of_nonneg f (fun _ => True) h0 h_one
    (fun x y _ _ => h_mul x y) (by simp) s (by simp)

omit [CommMonoid α] in

Depends on / 依赖: h_mul, h_one, le_prod_of_submultiplicative_on_pred_of_nonneg
-/
theorem Multiset.le_prod_of_submultiplicative_of_nonneg (f : α -> β) (h0 : forall a, 0 <= f a)
    (h_one : f 1 <= 1) (h_mul : forall a b, f (a * b) <= f a * f b) (s : Multiset α) :
    f s.prod <= (s.map f).prod :=
  le_prod_of_submultiplicative_on_pred_of_nonneg f (fun _ => True) h0 h_one
    (fun x y _ _ => h_mul x y) (by simp) s (by simp)

omit [CommMonoid α] in
/--
lemma `Multiset.mem_le_prod_of_one_le` / 引理 `Multiset.mem_le_prod_of_one_le`

English:
lemma Multiset.mem_le_prod_of_one_le
  statement: [ZeroLEOneClass β] {f : α -> β} (h1 : forall a : α, 1 <= f a)
  proof: by
  obtain ⟨s', rfl⟩ := exists_cons_of_mem ha
  rw [map_cons]; rw [prod_cons]
  calc f a = f a * 1 := (mul_one (f a)).symm
    _ <= f a * (s'.map f).prod := by
      gcongr
      · exact le_trans (zero_le_one' β) (h1 a)
      · simp_all [one_le_prod]

中文:
引理 Multiset.mem_le_prod_of_one_le
  结论: [ZeroLEOneClass β] {f : α -> β} (h1 : 对任意 a : α, 1 <= f a)
  证明: by
  obtain ⟨s', rfl⟩ := exists_cons_of_mem ha
  rw [map_cons]; rw [prod_cons]
  calc f a = f a * 1 := (mul_one (f a)).symm
    _ <= f a * (s'.map f).prod := by
      gcongr
      · exact le_trans (zero_le_one' β) (h1 a)
      · simp_all [one_le_prod]

Depends on / 依赖: exists_cons_of_mem, le_trans, map_cons, mul_one, one_le_prod, prod_cons, zero_le_one
-/
lemma Multiset.mem_le_prod_of_one_le [ZeroLEOneClass β] {f : α -> β} (h1 : forall a : α, 1 <= f a)
    {s : Multiset α} {a : α} (ha : a in s) : f a <= (s.map f).prod := by
  obtain ⟨s', rfl⟩ := exists_cons_of_mem ha
  rw [map_cons]; rw [prod_cons]
  calc f a = f a * 1 := (mul_one (f a)).symm
    _ <= f a * (s'.map f).prod := by
      gcongr
      · exact le_trans (zero_le_one' β) (h1 a)
      · simp_all [one_le_prod]

end OrderedCommSemiring
