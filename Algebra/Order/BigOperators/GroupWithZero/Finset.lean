/-
Copyright (c) 2025 Michael Stoll, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Floris van Doorn
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Tactic.Ring

/-!
# Big operators on a finset in groups with zero involving order

This file contains the results concerning the interaction of finset big operators with groups with
zero, where order is involved.
-/

public section

variable {ι R S : Type*}

namespace Finset

section CommMonoidWithZero
variable [CommMonoidWithZero R]

section PosMulMono
variable [Preorder R] [ZeroLEOneClass R] [PosMulMono R] {f g : ι -> R} {s t : Finset ι}

/--
lemma `prod_nonneg` / 引理 `prod_nonneg`

English:
lemma prod_nonneg
  given: (h0 : forall i in s, 0 <= f i)
  statement: 0 <= ∏ i in s, f i
  proof: prod_induction f (fun i => 0 <= i) (fun _ _ ha hb => mul_nonneg ha hb) zero_le_one h0

中文:
引理 prod_nonneg
  条件: (h0 : 对任意 i in s, 0 <= f i)
  结论: 0 <= ∏ i in s, f i
  证明: prod_induction f (fun i => 0 <= i) (fun _ _ ha hb => mul_nonneg ha hb) zero_le_one h0

Depends on / 依赖: mul_nonneg, prod_induction, zero_le_one
-/
lemma prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ i in s, f i :=
  prod_induction f (fun i => 0 <= i) (fun _ _ ha hb => mul_nonneg ha hb) zero_le_one h0

/-- If all `f i`, `i ∈ s`, are nonnegative and each `f i` is less than or equal to `g i`, then the
product of `f i` is less than or equal to the product of `g i`. See also `Finset.prod_le_prod'` for
the case of an ordered commutative multiplicative monoid. -/
@[gcongr]
/--
lemma `prod_le_prod` / 引理 `prod_le_prod`

English:
lemma prod_le_prod
  given: (h0 : forall i in s, 0 <= f i) (h1 : forall i in s, f i <= g i)
  proof: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    simp only [prod_cons, forall_mem_cons] at h0 h1 ⊢
    have := posMulMono_iff_mulPosMono.1 ‹PosMulMono R›
    gcongr
    exacts [prod_nonneg h0.2, h0.1.trans h1.1, h1.1, ih h0.2 h1.2]

中文:
引理 prod_le_prod
  条件: (h0 : 对任意 i in s, 0 <= f i) (h1 : 对任意 i in s, f i <= g i)
  证明: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    simp only [prod_cons, forall_mem_cons] at h0 h1 ⊢
    have := posMulMono_iff_mulPosMono.1 ‹PosMulMono R›
    gcongr
    exacts [prod_nonneg h0.2, h0.1.trans h1.1, h1.1, ih h0.2 h1.2]

Depends on / 依赖: Finset, Finset.cons_induction, PosMulMono, cons_induction, exacts, forall_mem_cons, posMulMono_iff_mulPosMono, prod_cons, prod_nonneg
-/
lemma prod_le_prod (h0 : forall i in s, 0 <= f i) (h1 : forall i in s, f i <= g i) :
    ∏ i in s, f i <= ∏ i in s, g i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    simp only [prod_cons, forall_mem_cons] at h0 h1 ⊢
    have := posMulMono_iff_mulPosMono.1 ‹PosMulMono R›
    gcongr
    exacts [prod_nonneg h0.2, h0.1.trans h1.1, h1.1, ih h0.2 h1.2]

/--
theorem `_root_.Monotone.finsetProd` / 定理 `_root_.Monotone.finsetProd`

English:
theorem _root_.Monotone.finsetProd
  statement: {γ : Type*} [Preorder γ] {f : ι -> γ -> R}
  proof: fun _ _ hab => prod_le_prod (fun i hi => hf₀ i hi _) fun i hi => hf i hi hab

中文:
定理 _root_.递增.finsetProd
  结论: {γ : 类型} [预序 γ] {f : ι -> γ -> R}
  证明: fun _ _ hab => prod_le_prod (fun i hi => hf₀ i hi _) fun i hi => hf i hi hab

Depends on / 依赖: prod_le_prod
-/
theorem _root_.Monotone.finsetProd {γ : Type*} [Preorder γ] {f : ι -> γ -> R}
    (hf : forall i in s, Monotone (f i)) (hf₀ : forall i in s, forall x, 0 <= f i x) :
    Monotone fun x => ∏ i in s, f i x :=
  fun _ _ hab => prod_le_prod (fun i hi => hf₀ i hi _) fun i hi => hf i hi hab

/--
theorem `_root_.MonotoneOn.finsetProd` / 定理 `_root_.MonotoneOn.finsetProd`

English:
theorem _root_.MonotoneOn.finsetProd
  statement: {γ : Type*} [Preorder γ] {u : Set γ} {f : ι -> γ -> R}
  proof: fun _ ha _ hb hab => prod_le_prod (fun i hi => hf₀ i hi _ ha) fun i hi => hf i hi ha hb hab

中文:
定理 _root_.MonotoneOn.finsetProd
  结论: {γ : 类型} [预序 γ] {u : 集合 γ} {f : ι -> γ -> R}
  证明: fun _ ha _ hb hab => prod_le_prod (fun i hi => hf₀ i hi _ ha) fun i hi => hf i hi ha hb hab

Depends on / 依赖: prod_le_prod
-/
theorem _root_.MonotoneOn.finsetProd {γ : Type*} [Preorder γ] {u : Set γ} {f : ι -> γ -> R}
    (hf : forall i in s, MonotoneOn (f i) u) (hf₀ : forall i in s, forall x in u, 0 <= f i x) :
    MonotoneOn (fun x => ∏ i in s, f i x) u :=
  fun _ ha _ hb hab => prod_le_prod (fun i hi => hf₀ i hi _ ha) fun i hi => hf i hi ha hb hab

/--
theorem `_root_.Antitone.finsetProd` / 定理 `_root_.Antitone.finsetProd`

English:
theorem _root_.Antitone.finsetProd
  statement: {γ : Type*} [Preorder γ] {f : ι -> γ -> R}
  proof: fun _ _ hab => prod_le_prod (fun i hi => hf₀ i hi _) fun i hi => hf i hi hab

中文:
定理 _root_.递减.finsetProd
  结论: {γ : 类型} [预序 γ] {f : ι -> γ -> R}
  证明: fun _ _ hab => prod_le_prod (fun i hi => hf₀ i hi _) fun i hi => hf i hi hab

Depends on / 依赖: prod_le_prod
-/
theorem _root_.Antitone.finsetProd {γ : Type*} [Preorder γ] {f : ι -> γ -> R}
    (hf : forall i in s, Antitone (f i)) (hf₀ : forall i in s, forall x, 0 <= f i x) :
    Antitone fun x => ∏ i in s, f i x :=
  fun _ _ hab => prod_le_prod (fun i hi => hf₀ i hi _) fun i hi => hf i hi hab

/--
theorem `_root_.AntitoneOn.finsetProd` / 定理 `_root_.AntitoneOn.finsetProd`

English:
theorem _root_.AntitoneOn.finsetProd
  statement: {γ : Type*} [Preorder γ] {u : Set γ} {f : ι -> γ -> R}
  proof: fun _ ha _ hb hab => prod_le_prod (fun i hi => hf₀ i hi _ hb) fun i hi => hf i hi ha hb hab

中文:
定理 _root_.AntitoneOn.finsetProd
  结论: {γ : 类型} [预序 γ] {u : 集合 γ} {f : ι -> γ -> R}
  证明: fun _ ha _ hb hab => prod_le_prod (fun i hi => hf₀ i hi _ hb) fun i hi => hf i hi ha hb hab

Depends on / 依赖: prod_le_prod
-/
theorem _root_.AntitoneOn.finsetProd {γ : Type*} [Preorder γ] {u : Set γ} {f : ι -> γ -> R}
    (hf : forall i in s, AntitoneOn (f i) u) (hf₀ : forall i in s, forall x in u, 0 <= f i x) :
    AntitoneOn (fun x => ∏ i in s, f i x) u :=
  fun _ ha _ hb hab => prod_le_prod (fun i hi => hf₀ i hi _ hb) fun i hi => hf i hi ha hb hab

/--
lemma `prod_le_one` / 引理 `prod_le_one`

English:
lemma prod_le_one
  given: (h0 : forall i in s, 0 <= f i) (h1 : forall i in s, f i <= 1)
  statement: ∏ i in s, f i <= 1
  proof: by
  convert! ← prod_le_prod h0 h1
  exact Finset.prod_const_one

中文:
引理 prod_le_one
  条件: (h0 : 对任意 i in s, 0 <= f i) (h1 : 对任意 i in s, f i <= 1)
  结论: ∏ i in s, f i <= 1
  证明: by
  convert! ← prod_le_prod h0 h1
  exact Finset.prod_const_one

Depends on / 依赖: Finset, Finset.prod_const_one, convert, prod_const_one, prod_le_prod
-/
lemma prod_le_one (h0 : forall i in s, 0 <= f i) (h1 : forall i in s, f i <= 1) : ∏ i in s, f i <= 1 := by
  convert! ← prod_le_prod h0 h1
  exact Finset.prod_const_one

/--
lemma `one_le_prod` / 引理 `one_le_prod`

English:
lemma one_le_prod
  given: (hf : forall i in s, 1 <= f i)
  statement: 1 <= ∏ i in s, f i
  proof: by
  simpa using prod_le_prod (by simp) hf

中文:
引理 one_le_prod
  条件: (hf : 对任意 i in s, 1 <= f i)
  结论: 1 <= ∏ i in s, f i
  证明: by
  simpa using prod_le_prod (by simp) hf

Depends on / 依赖: prod_le_prod
-/
lemma one_le_prod (hf : forall i in s, 1 <= f i) : 1 <= ∏ i in s, f i := by
  simpa using prod_le_prod (by simp) hf

/--
lemma `le_prod_max_one` / 引理 `le_prod_max_one`

English:
lemma le_prod_max_one
  statement: {M : Type*} [CommMonoidWithZero M] [LinearOrder M] [ZeroLEOneClass M]
  proof: by
  classical
  rcases lt_or_ge (f i) 0 with hf | hf
  · exact (hf.trans_le <| prod_nonneg fun _ _ => le_sup_of_le_right zero_le_one).le
  have : f i = ∏ j in s, if i = j then f i else 1 := by
    rw [prod_eq_single_of_mem i hi fun _ _ _ => by grind]
    simp
  exact this ▸ prod_le_prod (fun _ _ => by grind [zero_le_one]) fun _ _ => by grind

@[gcongr]

中文:
引理 le_prod_max_one
  结论: {M : 类型} [带零交换幺半群 M] [线性序 M] [ZeroLEOne类 M]
  证明: by
  classical
  rcases lt_or_ge (f i) 0 with hf | hf
  · exact (hf.trans_le <| prod_nonneg fun _ _ => le_sup_of_le_right zero_le_one).le
  have : f i = ∏ j in s, if i = j then f i else 1 := by
    rw [prod_eq_single_of_mem i hi fun _ _ _ => by grind]
    simp
  exact this ▸ prod_le_prod (fun _ _ => by grind [zero_le_one]) fun _ _ => by grind

@[gcongr]

Depends on / 依赖: classical, hf.trans_le, le_sup_of_le_right, lt_or_ge, prod_eq_single_of_mem, prod_le_prod, prod_nonneg, trans_le, zero_le_one
-/
lemma le_prod_max_one {M : Type*} [CommMonoidWithZero M] [LinearOrder M] [ZeroLEOneClass M]
    [PosMulMono M] {i : ι} (hi : i in s) (f : ι -> M) :
    f i <= ∏ i in s, max (f i) 1 := by
  classical
  rcases lt_or_ge (f i) 0 with hf | hf
  · exact (hf.trans_le <| prod_nonneg fun _ _ => le_sup_of_le_right zero_le_one).le
  have : f i = ∏ j in s, if i = j then f i else 1 := by
    rw [prod_eq_single_of_mem i hi fun _ _ _ => by grind]
    simp
  exact this ▸ prod_le_prod (fun _ _ => by grind [zero_le_one]) fun _ _ => by grind

@[gcongr]
/--
theorem `prod_le_prod_of_subset_of_one_le` / 定理 `prod_le_prod_of_subset_of_one_le`

English:
theorem prod_le_prod_of_subset_of_one_le
  statement: (h : s subseteq t)
  proof: by
  have := posMulMono_iff_mulPosMono.1 ‹PosMulMono R›
  classical
  calc
      ∏ i in s, f i <= (∏ i in t \ s, f i) * ∏ i in s, f i :=
le_mul_of_one_le_left (prod_nonneg hf0) one_le_prod by simpa only [mem_sdiff, and_imp]
      _ = ∏ i in t \ s union s, f i := (prod_union sdiff_disjoint).symm
      _ = ∏ i in t, f i := by rw [sdiff_union_of_subset h]

中文:
定理 prod_le_prod_of_subset_of_one_le
  结论: (h : s subseteq t)
  证明: by
  have := posMulMono_iff_mulPosMono.1 ‹PosMulMono R›
  classical
  calc
      ∏ i in s, f i <= (∏ i in t \ s, f i) * ∏ i in s, f i :=
le_mul_of_one_le_left (prod_nonneg hf0) one_le_prod by simpa only [mem_sdiff, and_imp]
      _ = ∏ i in t \ s union s, f i := (prod_union sdiff_disjoint).symm
      _ = ∏ i in t, f i := by rw [sdiff_union_of_subset h]

Depends on / 依赖: PosMulMono, and_imp, classical, le_mul_of_one_le_left, mem_sdiff, one_le_prod, posMulMono_iff_mulPosMono, prod_nonneg, prod_union, sdiff_disjoint, sdiff_union_of_subset
-/
theorem prod_le_prod_of_subset_of_one_le (h : s subseteq t)
    (hf0 : forall i in s, 0 <= f i)
    (hf : forall i in t, i ∉ s -> 1 <= f i) : ∏ i in s, f i <= ∏ i in t, f i := by
  have := posMulMono_iff_mulPosMono.1 ‹PosMulMono R›
  classical
  calc
      ∏ i in s, f i <= (∏ i in t \ s, f i) * ∏ i in s, f i :=
le_mul_of_one_le_left (prod_nonneg hf0) one_le_prod by simpa only [mem_sdiff, and_imp]
      _ = ∏ i in t \ s union s, f i := (prod_union sdiff_disjoint).symm
      _ = ∏ i in t, f i := by rw [sdiff_union_of_subset h]

/--
theorem `prod_le_prod_of_subset_of_le_one` / 定理 `prod_le_prod_of_subset_of_le_one`

English:
theorem prod_le_prod_of_subset_of_le_one
  statement: (h : s subseteq t) (hf0 : forall i in t, 0 <= f i)
  proof: by
  have := posMulMono_iff_mulPosMono.1 ‹PosMulMono R›
  classical
  calc
    ∏ i in t, f i = ∏ i in t \ s union s, f i := by rw [sdiff_union_of_subset h]
    _ = (∏ i in t \ s, f i) * ∏ i in s, f i := prod_union sdiff_disjoint
    _ <= ∏ i in s, f i :=
      mul_le_of_le_one_left (prod_nonneg (by grind)) (prod_le_one (by grind) (by grind))

中文:
定理 prod_le_prod_of_subset_of_le_one
  结论: (h : s subseteq t) (hf0 : 对任意 i in t, 0 <= f i)
  证明: by
  have := posMulMono_iff_mulPosMono.1 ‹PosMulMono R›
  classical
  calc
    ∏ i in t, f i = ∏ i in t \ s union s, f i := by rw [sdiff_union_of_subset h]
    _ = (∏ i in t \ s, f i) * ∏ i in s, f i := prod_union sdiff_disjoint
    _ <= ∏ i in s, f i :=
      mul_le_of_le_one_left (prod_nonneg (by grind)) (prod_le_one (by grind) (by grind))

Depends on / 依赖: PosMulMono, classical, mul_le_of_le_one_left, posMulMono_iff_mulPosMono, prod_le_one, prod_nonneg, prod_union, sdiff_disjoint, sdiff_union_of_subset
-/
theorem prod_le_prod_of_subset_of_le_one (h : s subseteq t) (hf0 : forall i in t, 0 <= f i)
    (hf : forall i in t, i ∉ s -> f i <= 1) :
    ∏ i in t, f i <= ∏ i in s, f i := by
  have := posMulMono_iff_mulPosMono.1 ‹PosMulMono R›
  classical
  calc
    ∏ i in t, f i = ∏ i in t \ s union s, f i := by rw [sdiff_union_of_subset h]
    _ = (∏ i in t \ s, f i) * ∏ i in s, f i := prod_union sdiff_disjoint
    _ <= ∏ i in s, f i :=
      mul_le_of_le_one_left (prod_nonneg (by grind)) (prod_le_one (by grind) (by grind))

/--
theorem `prod_mono_set_of_one_le` / 定理 `prod_mono_set_of_one_le`

English:
theorem prod_mono_set_of_one_le
  given: (hf : forall x, 1 <= f x)
  proof: fun _ _ hst => prod_le_prod_of_subset_of_one_le hst
    (fun i _ => zero_le_one.trans (hf i)) (fun x _ _ => hf x)

中文:
定理 prod_mono_set_of_one_le
  条件: (hf : 对任意 x, 1 <= f x)
  证明: fun _ _ hst => prod_le_prod_of_subset_of_one_le hst
    (fun i _ => zero_le_one.trans (hf i)) (fun x _ _ => hf x)

Depends on / 依赖: prod_le_prod_of_subset_of_one_le, zero_le_one, zero_le_one.trans
-/
theorem prod_mono_set_of_one_le (hf : forall x, 1 <= f x) :
    Monotone fun s => ∏ x in s, f x :=
  fun _ _ hst => prod_le_prod_of_subset_of_one_le hst
    (fun i _ => zero_le_one.trans (hf i)) (fun x _ _ => hf x)

/--
theorem `prod_anti_set_of_le_one` / 定理 `prod_anti_set_of_le_one`

English:
theorem prod_anti_set_of_le_one
  given: (hf0 : forall (x : ι), 0 <= f x) (hf : forall (x : ι), f x <= 1)
  proof: fun _ _ hst => prod_le_prod_of_subset_of_le_one hst (by grind) (by simp [hf])

中文:
定理 prod_anti_set_of_le_one
  条件: (hf0 : 对任意 (x : ι), 0 <= f x) (hf : 对任意 (x : ι), f x <= 1)
  证明: fun _ _ hst => prod_le_prod_of_subset_of_le_one hst (by grind) (by simp [hf])

Depends on / 依赖: prod_le_prod_of_subset_of_le_one
-/
theorem prod_anti_set_of_le_one (hf0 : forall (x : ι), 0 <= f x) (hf : forall (x : ι), f x <= 1) :
    Antitone fun (s : Finset ι) => ∏ x in s, f x :=
  fun _ _ hst => prod_le_prod_of_subset_of_le_one hst (by grind) (by simp [hf])

end PosMulMono

section PosMulStrictMono
variable [PartialOrder R] [ZeroLEOneClass R] [PosMulStrictMono R] [Nontrivial R] {f g : ι -> R}
  {s t : Finset ι}

/--
lemma `prod_pos` / 引理 `prod_pos`

English:
lemma prod_pos
  given: (h0 : forall i in s, 0 < f i)
  statement: 0 < ∏ i in s, f i
  proof: prod_induction f (fun x => 0 < x) (fun _ _ ha hb => mul_pos ha hb) zero_lt_one h0

中文:
引理 prod_pos
  条件: (h0 : 对任意 i in s, 0 < f i)
  结论: 0 < ∏ i in s, f i
  证明: prod_induction f (fun x => 0 < x) (fun _ _ ha hb => mul_pos ha hb) zero_lt_one h0

Depends on / 依赖: mul_pos, prod_induction, zero_lt_one
-/
lemma prod_pos (h0 : forall i in s, 0 < f i) : 0 < ∏ i in s, f i :=
  prod_induction f (fun x => 0 < x) (fun _ _ ha hb => mul_pos ha hb) zero_lt_one h0

/--
lemma `prod_lt_prod` / 引理 `prod_lt_prod`

English:
lemma prod_lt_prod
  statement: (hf : forall i in s, 0 < f i) (hfg : forall i in s, f i <= g i)
  proof: by
  classical
  obtain ⟨i, hi, hilt⟩ := hlt
  rw [← insert_erase hi]; rw [prod_insert (notMem_erase _ _)]; rw [prod_insert (notMem_erase _ _)]
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹PosMulStrictMono R›
  refine mul_lt_mul_of_pos_of_nonneg' hilt ?_ ?_ ?_
  · exact prod_le_prod (fun j hj => le_of_lt (hf j (mem_of_mem_erase hj)))
      (fun _ hj => hfg _ <| mem_of_mem_erase hj)
  · exact prod_pos fun j hj => hf j (mem_of_mem_erase hj)
  · exact (hf i hi).le.trans hilt.le

中文:
引理 prod_lt_prod
  结论: (hf : 对任意 i in s, 0 < f i) (hfg : 对任意 i in s, f i <= g i)
  证明: by
  classical
  obtain ⟨i, hi, hilt⟩ := hlt
  rw [← insert_erase hi]; rw [prod_insert (notMem_erase _ _)]; rw [prod_insert (notMem_erase _ _)]
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹PosMulStrictMono R›
  refine mul_lt_mul_of_pos_of_nonneg' hilt ?_ ?_ ?_
  · exact prod_le_prod (fun j hj => le_of_lt (hf j (mem_of_mem_erase hj)))
      (fun _ hj => hfg _ <| mem_of_mem_erase hj)
  · exact prod_pos fun j hj => hf j (mem_of_mem_erase hj)
  · exact (hf i hi).le.trans hilt.le

Depends on / 依赖: PosMulStrictMono, classical, hilt.le, insert_erase, le.trans, le_of_lt, mem_of_mem_erase, mul_lt_mul_of_pos_of_nonneg, notMem_erase, posMulStrictMono_iff_mulPosStrictMono, prod_insert, prod_le_prod, prod_pos
-/
lemma prod_lt_prod (hf : forall i in s, 0 < f i) (hfg : forall i in s, f i <= g i)
    (hlt : exists i in s, f i < g i) :
    ∏ i in s, f i < ∏ i in s, g i := by
  classical
  obtain ⟨i, hi, hilt⟩ := hlt
  rw [← insert_erase hi]; rw [prod_insert (notMem_erase _ _)]; rw [prod_insert (notMem_erase _ _)]
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹PosMulStrictMono R›
  refine mul_lt_mul_of_pos_of_nonneg' hilt ?_ ?_ ?_
  · exact prod_le_prod (fun j hj => le_of_lt (hf j (mem_of_mem_erase hj)))
      (fun _ hj => hfg _ <| mem_of_mem_erase hj)
  · exact prod_pos fun j hj => hf j (mem_of_mem_erase hj)
  · exact (hf i hi).le.trans hilt.le

/--
lemma `prod_lt_prod_of_nonempty` / 引理 `prod_lt_prod_of_nonempty`

English:
lemma prod_lt_prod_of_nonempty
  statement: (hf : forall i in s, 0 < f i) (hfg : forall i in s, f i < g i)
  proof: by
  apply prod_lt_prod hf fun i hi => le_of_lt (hfg i hi)
  obtain ⟨i, hi⟩ := h_ne
  exact ⟨i, hi, hfg i hi⟩

中文:
引理 prod_lt_prod_of_nonempty
  结论: (hf : 对任意 i in s, 0 < f i) (hfg : 对任意 i in s, f i < g i)
  证明: by
  apply prod_lt_prod hf fun i hi => le_of_lt (hfg i hi)
  obtain ⟨i, hi⟩ := h_ne
  exact ⟨i, hi, hfg i hi⟩

Depends on / 依赖: h_ne, le_of_lt, prod_lt_prod
-/
lemma prod_lt_prod_of_nonempty (hf : forall i in s, 0 < f i) (hfg : forall i in s, f i < g i)
    (h_ne : s.Nonempty) :
    ∏ i in s, f i < ∏ i in s, g i := by
  apply prod_lt_prod hf fun i hi => le_of_lt (hfg i hi)
  obtain ⟨i, hi⟩ := h_ne
  exact ⟨i, hi, hfg i hi⟩

end PosMulStrictMono
end CommMonoidWithZero

end Finset
