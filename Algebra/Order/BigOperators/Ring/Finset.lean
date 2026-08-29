/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Multiset
public import Mathlib.Tactic.Ring

/-!
# Big operators on a finset in ordered rings

This file contains the results concerning the interaction of finset big operators with ordered
rings.

In particular, this file contains the standard form of the Cauchy-Schwarz inequality, as well as
some of its immediate consequences.
-/

public section

variable {ι R S : Type*}

namespace Finset

section OrderedSemiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {f : ι -> R} {s : Finset ι}

/--
lemma `sum_sq_le_sq_sum_of_nonneg` / 引理 `sum_sq_le_sq_sum_of_nonneg`

English:
lemma sum_sq_le_sq_sum_of_nonneg
  given: (hf : forall i in s, 0 <= f i)
  proof: by
  simp only [sq, sum_mul_sum]
  refine sum_le_sum fun i hi => ?_
  rw [← mul_sum]
  gcongr
  · exact hf i hi
  · exact single_le_sum hf hi

中文:
引理 sum_sq_le_sq_sum_of_nonneg
  条件: (hf : 对任意 i in s, 0 <= f i)
  证明: by
  simp only [sq, sum_mul_sum]
  refine sum_le_sum fun i hi => ?_
  rw [← mul_sum]
  gcongr
  · exact hf i hi
  · exact single_le_sum hf hi

Depends on / 依赖: mul_sum, single_le_sum, sum_le_sum, sum_mul_sum
-/
lemma sum_sq_le_sq_sum_of_nonneg (hf : forall i in s, 0 <= f i) :
    ∑ i in s, f i ^ 2 <= (∑ i in s, f i) ^ 2 := by
  simp only [sq, sum_mul_sum]
  refine sum_le_sum fun i hi => ?_
  rw [← mul_sum]
  gcongr
  · exact hf i hi
  · exact single_le_sum hf hi

end OrderedSemiring

section OrderedCommSemiring
variable [CommSemiring R] [PartialOrder R] [IsOrderedRing R] {f g : ι -> R} {s t : Finset ι}

/--
lemma `prod_add_prod_le` / 引理 `prod_add_prod_le`

English:
lemma prod_add_prod_le
  statement: {i : ι} {f g h : ι -> R} (hi : i in s) (h2i : g i + h i <= f i)
  proof: by
  classical
  simp_rw [prod_eq_mul_prod_sdiff_singleton_of_mem hi]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right h2i ?_)
  · rw [right_distrib]
    gcongr with j hj <;> aesop
  · apply prod_nonneg
    simp only [and_imp, mem_sdiff, mem_singleton]
    exact fun j hj hji => le_trans (hg j hj) (hgf j hj hji)

中文:
引理 prod_add_prod_le
  结论: {i : ι} {f g h : ι -> R} (hi : i in s) (h2i : g i + h i <= f i)
  证明: by
  classical
  simp_rw [prod_eq_mul_prod_sdiff_singleton_of_mem hi]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right h2i ?_)
  · rw [right_distrib]
    gcongr with j hj <;> aesop
  · apply prod_nonneg
    simp only [and_imp, mem_sdiff, mem_singleton]
    exact fun j hj hji => le_trans (hg j hj) (hgf j hj hji)

Depends on / 依赖: and_imp, classical, le_trans, mem_sdiff, mem_singleton, mul_le_mul_of_nonneg_right, prod_eq_mul_prod_sdiff_singleton_of_mem, prod_nonneg, right_distrib, simp_rw
-/
lemma prod_add_prod_le {i : ι} {f g h : ι -> R} (hi : i in s) (h2i : g i + h i <= f i)
    (hgf : forall j in s, j != i -> g j <= f j) (hhf : forall j in s, j != i -> h j <= f j) (hg : forall i in s, 0 <= g i)
    (hh : forall i in s, 0 <= h i) : ((∏ i in s, g i) + ∏ i in s, h i) <= ∏ i in s, f i := by
  classical
  simp_rw [prod_eq_mul_prod_sdiff_singleton_of_mem hi]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right h2i ?_)
  · rw [right_distrib]
    gcongr with j hj <;> aesop
  · apply prod_nonneg
    simp only [and_imp, mem_sdiff, mem_singleton]
    exact fun j hj hji => le_trans (hg j hj) (hgf j hj hji)

/--
theorem `le_prod_of_submultiplicative_on_pred_of_nonneg` / 定理 `le_prod_of_submultiplicative_on_pred_of_nonneg`

English:
theorem le_prod_of_submultiplicative_on_pred_of_nonneg
  statement: {M : Type*} [CommMonoid M] (f : M -> R)
  proof: by
  apply le_trans (Multiset.le_prod_of_submultiplicative_on_pred_of_nonneg f p h_nonneg h_one
    h_mul hp_mul _ ?_) (by simp [Multiset.map_map])
  intro _ ha
  obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp ha
  exact hps i hi

中文:
定理 le_prod_of_submultiplicative_on_pred_of_nonneg
  结论: {M : 类型} [交换幺半群 M] (f : M -> R)
  证明: by
  apply le_trans (Multiset.le_prod_of_submultiplicative_on_pred_of_nonneg f p h_nonneg h_one
    h_mul hp_mul _ ?_) (by simp [Multiset.map_map])
  intro _ ha
  obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp ha
  exact hps i hi

Depends on / 依赖: Multiset, Multiset.le_prod_of_submultiplicative_on_pred_of_nonneg, Multiset.map_map, Multiset.mem_map.mp, h_mul, h_nonneg, h_one, hp_mul, le_prod_of_submultiplicative_on_pred_of_nonneg, le_trans, map_map, mem_map
-/
theorem le_prod_of_submultiplicative_on_pred_of_nonneg {M : Type*} [CommMonoid M] (f : M -> R)
    (p : M -> Prop) (h_nonneg : forall a, 0 <= f a) (h_one : f 1 <= 1)
    (h_mul : forall a b, p a -> p b -> f (a * b) <= f a * f b) (hp_mul : forall a b, p a -> p b -> p (a * b))
    (s : Finset ι) (g : ι -> M) (hps : forall a, a in s -> p (g a)) :
    f (∏ i in s, g i) <= ∏ i in s, f (g i) := by
  apply le_trans (Multiset.le_prod_of_submultiplicative_on_pred_of_nonneg f p h_nonneg h_one
    h_mul hp_mul _ ?_) (by simp [Multiset.map_map])
  intro _ ha
  obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp ha
  exact hps i hi

/--
theorem `le_prod_of_submultiplicative_of_nonneg` / 定理 `le_prod_of_submultiplicative_of_nonneg`

English:
theorem le_prod_of_submultiplicative_of_nonneg
  statement: {M : Type*} [CommMonoid M]
  proof: le_trans (Multiset.le_prod_of_submultiplicative_of_nonneg f h_nonneg h_one h_mul _)
    (by simp [Multiset.map_map])

中文:
定理 le_prod_of_submultiplicative_of_nonneg
  结论: {M : 类型} [交换幺半群 M]
  证明: le_trans (Multiset.le_prod_of_submultiplicative_of_nonneg f h_nonneg h_one h_mul _)
    (by simp [Multiset.map_map])

Depends on / 依赖: Multiset, Multiset.le_prod_of_submultiplicative_of_nonneg, Multiset.map_map, h_mul, h_nonneg, h_one, le_prod_of_submultiplicative_of_nonneg, le_trans, map_map
-/
theorem le_prod_of_submultiplicative_of_nonneg {M : Type*} [CommMonoid M]
    (f : M -> R) (h_nonneg : forall a, 0 <= f a) (h_one : f 1 <= 1)
    (h_mul : forall x y : M, f (x * y) <= f x * f y) (s : Finset ι) (g : ι -> M) :
    f (∏ i in s, g i) <= ∏ i in s, f (g i) :=
  le_trans (Multiset.le_prod_of_submultiplicative_of_nonneg f h_nonneg h_one h_mul _)
    (by simp [Multiset.map_map])

end OrderedCommSemiring

/--
theorem `sum_mul_self_eq_zero_iff` / 定理 `sum_mul_self_eq_zero_iff`

English:
theorem sum_mul_self_eq_zero_iff
  statement: [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
  proof: by
  rw [sum_eq_zero_iff_of_nonneg fun _ _ => mul_self_nonneg _]
  simp

中文:
定理 sum_mul_self_eq_zero_iff
  结论: [半环 R] [线性序 R] [是StrictOrdered环 R]
  证明: by
  rw [sum_eq_zero_iff_of_nonneg fun _ _ => mul_self_nonneg _]
  simp

Depends on / 依赖: mul_self_nonneg, sum_eq_zero_iff_of_nonneg
-/
theorem sum_mul_self_eq_zero_iff [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [ExistsAddOfLE R] (s : Finset ι)
    (f : ι -> R) : ∑ i in s, f i * f i = 0 ↔ forall i in s, f i = 0 := by
  rw [sum_eq_zero_iff_of_nonneg fun _ _ => mul_self_nonneg _]
  simp

/--
lemma `abs_prod` / 引理 `abs_prod`

English:
lemma abs_prod
  given: [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (s : Finset ι) (f : ι -> R)
  proof: map_prod absHom _ _

@[simp, norm_cast]

中文:
引理 abs_prod
  条件: [交换环 R] [线性序 R] [是StrictOrdered环 R] (s : 有限集 ι) (f : ι -> R)
  证明: map_prod absHom _ _

@[simp, norm_cast]

Depends on / 依赖: absHom, map_prod
-/
lemma abs_prod [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (s : Finset ι) (f : ι -> R) :
    |∏ x in s, f x| = ∏ x in s, |f x| :=
  map_prod absHom _ _

@[simp, norm_cast]
/--
theorem `PNat.coe_prod` / 定理 `PNat.coe_prod`

English:
theorem PNat.coe_prod
  given: {ι : Type*} (f : ι -> Nat+) (s : Finset ι)
  proof: map_prod PNat.coeMonoidHom _ _

中文:
定理 正自然数.coe_prod
  条件: {ι : 类型} (f : ι -> 自然数+) (s : 有限集 ι)
  证明: map_prod PNat.coeMonoidHom _ _

Depends on / 依赖: PNat.coeMonoidHom, coeMonoidHom, map_prod
-/
theorem PNat.coe_prod {ι : Type*} (f : ι -> Nat+) (s : Finset ι) :
    ↑(∏ i in s, f i) = (∏ i in s, f i : Nat) :=
  map_prod PNat.coeMonoidHom _ _

section CanonicallyOrderedAdd
variable [CommSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
  {f g h : ι -> R} {s : Finset ι} {i : ι}

/--
lemma `_root_.CanonicallyOrderedAdd.prod_pos` / 引理 `_root_.CanonicallyOrderedAdd.prod_pos`

English:
lemma _root_.CanonicallyOrderedAdd.prod_pos
  given: [NoZeroDivisors R] [Nontrivial R]
  proof: CanonicallyOrderedAdd.multiset_prod_pos.trans Multiset.forall_mem_map_iff

中文:
引理 _root_.典范有序加法.prod_pos
  条件: [无零因子 R] [非平凡 R]
  证明: CanonicallyOrderedAdd.multiset_prod_pos.trans Multiset.forall_mem_map_iff
-/
@[simp] lemma _root_.CanonicallyOrderedAdd.prod_pos [NoZeroDivisors R] [Nontrivial R] :
    0 < ∏ i in s, f i ↔ (forall i in s, (0 : R) < f i) :=
  CanonicallyOrderedAdd.multiset_prod_pos.trans Multiset.forall_mem_map_iff

/--
lemma `prod_add_prod_le'` / 引理 `prod_add_prod_le'`

English:
lemma prod_add_prod_le'
  statement: (hi : i in s) (h2i : g i + h i <= f i) (hgf : forall j in s, j != i -> g j <= f j)
  proof: by
  classical
  simp_rw [prod_eq_mul_prod_sdiff_singleton_of_mem hi]
  grw [← h2i, right_distrib]
  gcongr with j hj j hj <;> simp_all

中文:
引理 prod_add_prod_le'
  结论: (hi : i in s) (h2i : g i + h i <= f i) (hgf : 对任意 j in s, j != i -> g j <= f j)
  证明: by
  classical
  simp_rw [prod_eq_mul_prod_sdiff_singleton_of_mem hi]
  grw [← h2i, right_distrib]
  gcongr with j hj j hj <;> simp_all

Depends on / 依赖: classical, prod_eq_mul_prod_sdiff_singleton_of_mem, right_distrib, simp_rw
-/
lemma prod_add_prod_le' (hi : i in s) (h2i : g i + h i <= f i) (hgf : forall j in s, j != i -> g j <= f j)
    (hhf : forall j in s, j != i -> h j <= f j) : ((∏ i in s, g i) + ∏ i in s, h i) <= ∏ i in s, f i := by
  classical
  simp_rw [prod_eq_mul_prod_sdiff_singleton_of_mem hi]
  grw [← h2i, right_distrib]
  gcongr with j hj j hj <;> simp_all

end CanonicallyOrderedAdd

/-! ### Named inequalities -/

/--
lemma `sum_sq_le_sum_mul_sum_of_sq_le_mul` / 引理 `sum_sq_le_sum_mul_sum_of_sq_le_mul`

English:
lemma sum_sq_le_sum_mul_sum_of_sq_le_mul
  statement: [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]
  proof: by
  obtain h | h := (sum_nonneg hg).eq_or_lt'
  · have ht' : ∑ i in s, r i = 0 := sum_eq_zero fun i hi => by
      simpa [(sum_eq_zero_iff_of_nonneg hg).1 h i hi] using ht i hi
    rw [h]; rw [ht']
    simp
  · refine le_of_mul_le_mul_of_pos_left
      (le_of_add_le_add_left (a := (∑ i in s, g i) * (∑ i in s, r i) ^ 2) ?_) h
    calc
      _ = ∑ i in s, 2 * r i * (∑ j in s, g j) * (∑ j in s, r j) := by
          simp_rw [mul_assoc, ← mul_sum, ← sum_mul]; ring
      _ <= ∑ i in s, (f i * (∑ j in s, g j) ^ 2 + g i * (∑ j in s, r j) ^ 2) := by
          gcongr with i hi
          have ht : (r i * (∑ j in s, g j) * (∑ j in s, r j)) ^ 2 <=
              (f i * (∑ j in s, g j) ^ 2) * (g i * (∑ j in s, r j) ^ 2) := by
            grw [mul_mul_mul_comm, ← mul_pow, mul_assoc, mul_pow, ht i hi]
            exact sq_nonneg _
          refine le_of_eq_of_le ?_ (two_mul_le_add_of_sq_le_mul
            (mul_nonneg (hf i hi) (sq_nonneg _)) (mul_nonneg (hg i hi) (sq_nonneg _)) ht)
          repeat rw [mul_assoc]
      _ = _ := by simp_rw [sum_add_distrib, ← sum_mul]; ring

@[deprecated sum_sq_le_sum_mul_sum_of_sq_le_mul (since := "2026-05-12")]

中文:
引理 sum_sq_le_sum_mul_sum_of_sq_le_mul
  结论: [交换半环 R] [线性序 R] [是StrictOrdered环 R]
  证明: by
  obtain h | h := (sum_nonneg hg).eq_or_lt'
  · have ht' : ∑ i in s, r i = 0 := sum_eq_zero fun i hi => by
      simpa [(sum_eq_zero_iff_of_nonneg hg).1 h i hi] using ht i hi
    rw [h]; rw [ht']
    simp
  · refine le_of_mul_le_mul_of_pos_left
      (le_of_add_le_add_left (a := (∑ i in s, g i) * (∑ i in s, r i) ^ 2) ?_) h
    calc
      _ = ∑ i in s, 2 * r i * (∑ j in s, g j) * (∑ j in s, r j) := by
          simp_rw [mul_assoc, ← mul_sum, ← sum_mul]; ring
      _ <= ∑ i in s, (f i * (∑ j in s, g j) ^ 2 + g i * (∑ j in s, r j) ^ 2) := by
          gcongr with i hi
          have ht : (r i * (∑ j in s, g j) * (∑ j in s, r j)) ^ 2 <=
              (f i * (∑ j in s, g j) ^ 2) * (g i * (∑ j in s, r j) ^ 2) := by
            grw [mul_mul_mul_comm, ← mul_pow, mul_assoc, mul_pow, ht i hi]
            exact sq_nonneg _
          refine le_of_eq_of_le ?_ (two_mul_le_add_of_sq_le_mul
            (mul_nonneg (hf i hi) (sq_nonneg _)) (mul_nonneg (hg i hi) (sq_nonneg _)) ht)
          repeat rw [mul_assoc]
      _ = _ := by simp_rw [sum_add_distrib, ← sum_mul]; ring

@[deprecated sum_sq_le_sum_mul_sum_of_sq_le_mul (since := "2026-05-12")]

Depends on / 依赖: eq_or_lt, le_of_add_le_add_left, le_of_mul_le_mul_of_pos_left, mul_assoc, mul_sum, simp_rw, sum_eq_zero, sum_eq_zero_iff_of_nonneg, sum_mul, sum_nonneg
-/
lemma sum_sq_le_sum_mul_sum_of_sq_le_mul [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [ExistsAddOfLE R]
    (s : Finset ι) {r f g : ι -> R} (hf : forall i in s, 0 <= f i) (hg : forall i in s, 0 <= g i)
    (ht : forall i in s, r i ^ 2 <= f i * g i) : (∑ i in s, r i) ^ 2 <= (∑ i in s, f i) * ∑ i in s, g i := by
  obtain h | h := (sum_nonneg hg).eq_or_lt'
  · have ht' : ∑ i in s, r i = 0 := sum_eq_zero fun i hi => by
      simpa [(sum_eq_zero_iff_of_nonneg hg).1 h i hi] using ht i hi
    rw [h]; rw [ht']
    simp
  · refine le_of_mul_le_mul_of_pos_left
      (le_of_add_le_add_left (a := (∑ i in s, g i) * (∑ i in s, r i) ^ 2) ?_) h
    calc
      _ = ∑ i in s, 2 * r i * (∑ j in s, g j) * (∑ j in s, r j) := by
          simp_rw [mul_assoc, ← mul_sum, ← sum_mul]; ring
      _ <= ∑ i in s, (f i * (∑ j in s, g j) ^ 2 + g i * (∑ j in s, r j) ^ 2) := by
          gcongr with i hi
          have ht : (r i * (∑ j in s, g j) * (∑ j in s, r j)) ^ 2 <=
              (f i * (∑ j in s, g j) ^ 2) * (g i * (∑ j in s, r j) ^ 2) := by
            grw [mul_mul_mul_comm, ← mul_pow, mul_assoc, mul_pow, ht i hi]
            exact sq_nonneg _
          refine le_of_eq_of_le ?_ (two_mul_le_add_of_sq_le_mul
            (mul_nonneg (hf i hi) (sq_nonneg _)) (mul_nonneg (hg i hi) (sq_nonneg _)) ht)
          repeat rw [mul_assoc]
      _ = _ := by simp_rw [sum_add_distrib, ← sum_mul]; ring

@[deprecated sum_sq_le_sum_mul_sum_of_sq_le_mul (since := "2026-05-12")]
/--
lemma `sum_sq_le_sum_mul_sum_of_sq_eq_mul` / 引理 `sum_sq_le_sum_mul_sum_of_sq_eq_mul`

English:
lemma sum_sq_le_sum_mul_sum_of_sq_eq_mul
  statement: [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]
  proof: sum_sq_le_sum_mul_sum_of_sq_le_mul s hf hg (fun i hi => (ht i hi).le)

中文:
引理 sum_sq_le_sum_mul_sum_of_sq_eq_mul
  结论: [交换半环 R] [线性序 R] [是StrictOrdered环 R]
  证明: sum_sq_le_sum_mul_sum_of_sq_le_mul s hf hg (fun i hi => (ht i hi).le)

Depends on / 依赖: sum_sq_le_sum_mul_sum_of_sq_le_mul
-/
lemma sum_sq_le_sum_mul_sum_of_sq_eq_mul [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [ExistsAddOfLE R]
    (s : Finset ι) {r f g : ι -> R} (hf : forall i in s, 0 <= f i) (hg : forall i in s, 0 <= g i)
    (ht : forall i in s, r i ^ 2 = f i * g i) : (∑ i in s, r i) ^ 2 <= (∑ i in s, f i) * ∑ i in s, g i :=
  sum_sq_le_sum_mul_sum_of_sq_le_mul s hf hg (fun i hi => (ht i hi).le)

/--
lemma `sum_mul_sq_le_sq_mul_sq` / 引理 `sum_mul_sq_le_sq_mul_sq`

English:
lemma sum_mul_sq_le_sq_mul_sq
  statement: [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]
  proof: sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun _ _ => sq_nonneg _) (fun _ _ => sq_nonneg _) (fun _ _ => (mul_pow ..).le)

中文:
引理 sum_mul_sq_le_sq_mul_sq
  结论: [交换半环 R] [线性序 R] [是StrictOrdered环 R]
  证明: sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun _ _ => sq_nonneg _) (fun _ _ => sq_nonneg _) (fun _ _ => (mul_pow ..).le)

Depends on / 依赖: mul_pow, sq_nonneg, sum_sq_le_sum_mul_sum_of_sq_le_mul
-/
lemma sum_mul_sq_le_sq_mul_sq [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [ExistsAddOfLE R] (s : Finset ι)
    (f g : ι -> R) : (∑ i in s, f i * g i) ^ 2 <= (∑ i in s, f i ^ 2) * ∑ i in s, g i ^ 2 :=
  sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun _ _ => sq_nonneg _) (fun _ _ => sq_nonneg _) (fun _ _ => (mul_pow ..).le)

/--
theorem `sq_sum_div_le_sum_sq_div` / 定理 `sq_sum_div_le_sum_sq_div`

English:
theorem sq_sum_div_le_sum_sq_div
  statement: [Semifield R] [LinearOrder R] [IsStrictOrderedRing R]
  proof: by
  have hg' : forall i in s, 0 <= g i := fun i hi => (hg i hi).le
  have H : forall i in s, 0 <= f i ^ 2 / g i := fun i hi => div_nonneg (sq_nonneg _) (hg' i hi)
  refine div_le_of_le_mul₀ (sum_nonneg hg') (sum_nonneg H)
    (sum_sq_le_sum_mul_sum_of_sq_le_mul _ H hg' fun i hi => ?_)
  rw [div_mul_cancel₀]
  exact (hg i hi).ne'

中文:
定理 sq_sum_div_le_sum_sq_div
  结论: [半域 R] [线性序 R] [是StrictOrdered环 R]
  证明: by
  have hg' : forall i in s, 0 <= g i := fun i hi => (hg i hi).le
  have H : forall i in s, 0 <= f i ^ 2 / g i := fun i hi => div_nonneg (sq_nonneg _) (hg' i hi)
  refine div_le_of_le_mul₀ (sum_nonneg hg') (sum_nonneg H)
    (sum_sq_le_sum_mul_sum_of_sq_le_mul _ H hg' fun i hi => ?_)
  rw [div_mul_cancel₀]
  exact (hg i hi).ne'

Depends on / 依赖: div_nonneg, sq_nonneg, sum_nonneg, sum_sq_le_sum_mul_sum_of_sq_le_mul
-/
theorem sq_sum_div_le_sum_sq_div [Semifield R] [LinearOrder R] [IsStrictOrderedRing R]
    [ExistsAddOfLE R] (s : Finset ι)
    (f : ι -> R) {g : ι -> R} (hg : forall i in s, 0 < g i) :
    (∑ i in s, f i) ^ 2 / ∑ i in s, g i <= ∑ i in s, f i ^ 2 / g i := by
  have hg' : forall i in s, 0 <= g i := fun i hi => (hg i hi).le
  have H : forall i in s, 0 <= f i ^ 2 / g i := fun i hi => div_nonneg (sq_nonneg _) (hg' i hi)
  refine div_le_of_le_mul₀ (sum_nonneg hg') (sum_nonneg H)
    (sum_sq_le_sum_mul_sum_of_sq_le_mul _ H hg' fun i hi => ?_)
  rw [div_mul_cancel₀]
  exact (hg i hi).ne'

end Finset

/-! ### Absolute values -/

section AbsoluteValue

/--
lemma `AbsoluteValue.sum_le` / 引理 `AbsoluteValue.sum_le`

English:
lemma AbsoluteValue.sum_le
  statement: [Semiring R] [Semiring S] [PartialOrder S] [IsOrderedRing S]
  proof: Finset.le_sum_of_subadditive abv (map_zero _).le abv.add_le _ _

中文:
引理 绝对值.sum_le
  结论: [半环 R] [半环 S] [偏序 S] [是Ordered环 S]
  证明: Finset.le_sum_of_subadditive abv (map_zero _).le abv.add_le _ _

Depends on / 依赖: Finset, Finset.le_sum_of_subadditive, abv.add_le, add_le, le_sum_of_subadditive, map_zero
-/
lemma AbsoluteValue.sum_le [Semiring R] [Semiring S] [PartialOrder S] [IsOrderedRing S]
    (abv : AbsoluteValue R S)
    (s : Finset ι) (f : ι -> R) : abv (∑ i in s, f i) <= ∑ i in s, abv (f i) :=
  Finset.le_sum_of_subadditive abv (map_zero _).le abv.add_le _ _

/--
lemma `IsAbsoluteValue.abv_sum` / 引理 `IsAbsoluteValue.abv_sum`

English:
lemma IsAbsoluteValue.abv_sum
  statement: [Semiring R] [Semiring S] [PartialOrder S] [IsOrderedRing S]
  proof: (IsAbsoluteValue.toAbsoluteValue abv).sum_le _ _

nonrec lemma AbsoluteValue.map_prod [CommSemiring R] [Nontrivial R]
    [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
    (abv : AbsoluteValue R S) (f : ι -> R) (s : Finset ι) :
    abv (∏ i in s, f i) = ∏ i in s, abv (f i) :=
  map_prod abv f s

中文:
引理 是绝对值.abv_sum
  结论: [半环 R] [半环 S] [偏序 S] [是Ordered环 S]
  证明: (IsAbsoluteValue.toAbsoluteValue abv).sum_le _ _

nonrec lemma AbsoluteValue.map_prod [CommSemiring R] [Nontrivial R]
    [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
    (abv : AbsoluteValue R S) (f : ι -> R) (s : Finset ι) :
    abv (∏ i in s, f i) = ∏ i in s, abv (f i) :=
  map_prod abv f s

Depends on / 依赖: IsAbsoluteValue, IsAbsoluteValue.toAbsoluteValue, sum_le, toAbsoluteValue
-/
lemma IsAbsoluteValue.abv_sum [Semiring R] [Semiring S] [PartialOrder S] [IsOrderedRing S]
    (abv : R -> S) [IsAbsoluteValue abv]
    (f : ι -> R) (s : Finset ι) : abv (∑ i in s, f i) <= ∑ i in s, abv (f i) :=
  (IsAbsoluteValue.toAbsoluteValue abv).sum_le _ _

nonrec lemma AbsoluteValue.map_prod [CommSemiring R] [Nontrivial R]
    [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
    (abv : AbsoluteValue R S) (f : ι -> R) (s : Finset ι) :
    abv (∏ i in s, f i) = ∏ i in s, abv (f i) :=
  map_prod abv f s

/--
lemma `IsAbsoluteValue.map_prod` / 引理 `IsAbsoluteValue.map_prod`

English:
lemma IsAbsoluteValue.map_prod
  statement: [CommSemiring R] [Nontrivial R]
  proof: (IsAbsoluteValue.toAbsoluteValue abv).map_prod _ _

中文:
引理 是绝对值.map_prod
  结论: [交换半环 R] [非平凡 R]
  证明: (IsAbsoluteValue.toAbsoluteValue abv).map_prod _ _

Depends on / 依赖: IsAbsoluteValue, IsAbsoluteValue.toAbsoluteValue, map_prod, toAbsoluteValue
-/
lemma IsAbsoluteValue.map_prod [CommSemiring R] [Nontrivial R]
    [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
    (abv : R -> S) [IsAbsoluteValue abv] (f : ι -> R) (s : Finset ι) :
    abv (∏ i in s, f i) = ∏ i in s, abv (f i) :=
  (IsAbsoluteValue.toAbsoluteValue abv).map_prod _ _

end AbsoluteValue

/-! ### Positivity extension -/

namespace Mathlib.Meta.Positivity
open Qq Lean Meta Finset

alias ⟨_, prod_ne_zero⟩ := prod_ne_zero_iff

attribute [local instance] monadLiftOptionMetaM in
/-- The `positivity` extension which proves that `∏ i ∈ s, f i` is nonnegative if `f` is, and
positive if each `f i` is.

TODO: The following example does not work
```
example (s : Finset ℕ) (f : ℕ → ℤ) (hf : ∀ n, 0 ≤ f n) : 0 ≤ s.prod f := by positivity
```
because `compareHyp` can't look for assumptions behind binders.
-/
@[positivity Finset.prod _ _]
meta def evalFinsetProd : PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match e with
  | ~q(@Finset.prod $ι _ $instα $s $f) =>
    let i : Q($ι) ← mkFreshExprMVarQ q($ι) .syntheticOpaque
    have body : Q($α) := Expr.betaRev f #[i]
    let rbody ← core zα pα body
    let _instαmon ← synthInstanceQ q(CommMonoidWithZero $α)
    -- Try to show that the product is positive
    let p_pos : Option Q(0 < $e) ← do
      let .positive pbody := rbody | pure none -- Fail if the body is not provably positive
      -- TODO(https://github.com/leanprover-community/quote4/issues/38):
      -- We must name the following, else `assertInstancesCommute` loops.
      let .some _instαzeroone ← trySynthInstanceQ q(ZeroLEOneClass $α) | pure none
      let .some _instαposmul ← trySynthInstanceQ q(PosMulStrictMono $α) | pure none
      let .some _instαnontriv ← trySynthInstanceQ q(Nontrivial $α) | pure none
      assertInstancesCommute
      let pr : Q(forall i, 0 < $f i) ← mkLambdaFVars #[i] pbody (binderInfoForMVars := .default)
pure some q(prod_pos fun i _ => $pr i)
    if let some p_pos := p_pos then return .positive p_pos
    -- Try to show that the product is nonnegative
    let p_nonneg : Option Q(0 <= $e) ← do
      let some pbody := rbody.toNonneg
        | pure none -- Fail if the body is not provably nonnegative
      let pr : Q(forall i, 0 <= $f i) ← mkLambdaFVars #[i] pbody (binderInfoForMVars := .default)
      -- TODO(https://github.com/leanprover-community/quote4/issues/38):
      -- We must name the following, else `assertInstancesCommute` loops.
      let .some _instαzeroone ← trySynthInstanceQ q(ZeroLEOneClass $α) | pure none
      let .some _instαposmul ← trySynthInstanceQ q(PosMulMono $α) | pure none
      assertInstancesCommute
pure some q(prod_nonneg fun i _ => $pr i)
    if let some p_nonneg := p_nonneg then return .nonnegative p_nonneg
    -- Fall back to showing that the product is nonzero
    let pbody ← rbody.toNonzero
    let pr : Q(forall i, $f i != 0) ← mkLambdaFVars #[i] pbody (binderInfoForMVars := .default)
    -- TODO(https://github.com/leanprover-community/quote4/issues/38):
    -- We must name the following, else `assertInstancesCommute` loops.
    let _instαnontriv ← synthInstanceQ q(Nontrivial $α)
    let _instαnozerodiv ← synthInstanceQ q(NoZeroDivisors $α)
    assertInstancesCommute
    return .nonzero q(prod_ne_zero fun i _ => $pr i)

end Mathlib.Meta.Positivity
