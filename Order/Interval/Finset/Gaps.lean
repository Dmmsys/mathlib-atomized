/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Prod.Lex

/-!
# Gaps of disjoint closed intervals

This file defines `Finset.intervalGapsWithin` that computes the complement of the union of a
collection of pairwise disjoint subintervals of `[a, b]`.

If `LinearOrder α`, `F` is a finite subset of `α × α` such that for any `(x, y) ∈ F`,
`a ≤ x ≤ y ≤ b` and all such `[x, y]`'s are pairwise disjoint, `h` is a proof of `F.card = k`,
`i` is in `Fin (k + 1)`, we order `F` from left to right as
`(x 0, y 0), ..., (x (k - 1), y (k - 1))`, then `F.intervalGapsWithin h a b i` is
- `(a, b)` if `0 = i = k`;
- `(a, x 0)` if `0 = i < k`;
- `(y (i - 1), x i)` if `0 < i < k`;
- `(y (i - 1), b)` if `0 < i = k`.

Technically, the definition `F.intervalGapsWithin a b` does not require `F` to be pairwise disjoint
or endpoints to be within `[a, b]` or even require that `a ≤ b`, but it makes the most sense if
they are actually satisfied. If they are actually satisfied, then we show that
* `Finset.intervalGapsWithin_mapsTo`, `Finset.intervalGapsWithin_injective`,
  `Finset.intervalGapsWithin_surjOn`:
  `(fun j ↦ ((F.intervalGapsWithin h a b j.castSucc).2, (F.intervalGapsWithin h a b j.succ).1))` is
  a bijection between `Set.Iio k` and `F`.
* `Finset.intervalGapsWithin_le_fst`, `Finset.intervalGapsWithin_snd_le`,
  `Finset.intervalGapsWithin_fst_le_snd`:
  `[(F.intervalGapsWithin h a b j).1, (F.intervalGapsWithin h a b j).2]` is indeed a subinterval of
  `[a, b]` when `j < k`.
* `Finset.intervalGapsWithin_pairwiseDisjoint_Ioc`: the half-closed intervals
  `[(F.intervalGapsWithin h a b j).1, (F.intervalGapsWithin h a b j).2)` are pairwise disjoint
  for `j < k + 1`.
-/

@[expose] public section

open Fin Fin.NatCast Set

section IntervalGapsWithin

namespace Finset

variable {α : Type*} [LinearOrder α] (F : Finset (α × α)) {k : Nat} (h : F.card = k) (a b : α)
  (j : Nat)

/--
Definition of `intervalGapsWithin` / `intervalGapsWithin` 的定义

English:
definition intervalGapsWithin
  signature: (i : Fin (k + 1))
  body: (fst, snd) where
  /-- The first coordinate of `F.intervalGapsWithin h a b i` is `a` if `i = 0`,
  `y (i - 1)` otherwise. -/
  fst := if hi : i = 0 then a else
.2 F.orderEmbOfFin (α := α ×ₗ α) h (i.pred hi)
  /-- The second coordinate of `F.intervalGapsWithin h a b i` is `b` if `i = k`,
  `x i` othe

中文:
定义 intervalGapsWithin
  签名: (i : 有限集 (k + 1))
  定义体: (fst, snd) where
  /-- The first coordinate of `F.intervalGapsWithin h a b i` is `a` if `i = 0`,
  `y (i - 1)` otherwise. -/
  fst := if hi : i = 0 then a else
.2 F.orderEmbOfFin (α := α ×ₗ α) h (i.pred hi)
  /-- The second coordinate of `F.intervalGapsWithin h a b i` is `b` if `i = k`,
  `x i` othe
-/
noncomputable def intervalGapsWithin (i : Fin (k + 1)) : α × α := (fst, snd) where
  /-- The first coordinate of `F.intervalGapsWithin h a b i` is `a` if `i = 0`,
  `y (i - 1)` otherwise. -/
  fst := if hi : i = 0 then a else
.2 F.orderEmbOfFin (α := α ×ₗ α) h (i.pred hi)
  /-- The second coordinate of `F.intervalGapsWithin h a b i` is `b` if `i = k`,
  `x i` otherwise. -/
  snd := if hi : i = last k then b else
.1 F.orderEmbOfFin (α := α ×ₗ α) h (i.castPred hi)

@[simp]
/--
theorem `intervalGapsWithin_zero_fst` / 定理 `intervalGapsWithin_zero_fst`

English:
theorem intervalGapsWithin_zero_fst
  statement: (F.intervalGapsWithin h a b 0).1 = a
  proof: by
  simp [intervalGapsWithin, intervalGapsWithin.fst]

中文:
定理 intervalGapsWithin_zero_fst
  结论: (F.intervalGapsWithin h a b 0).1 = a
  证明: by
  simp [intervalGapsWithin, intervalGapsWithin.fst]

Depends on / 依赖: intervalGapsWithin, intervalGapsWithin.fst
-/
theorem intervalGapsWithin_zero_fst : (F.intervalGapsWithin h a b 0).1 = a := by
  simp [intervalGapsWithin, intervalGapsWithin.fst]

/--
theorem `intervalGapsWithin_succ_fst_of_lt` / 定理 `intervalGapsWithin_succ_fst_of_lt`

English:
theorem intervalGapsWithin_succ_fst_of_lt
  given: (hj : j < k)
  proof: by
  have : (j.succ : Fin (k + 1)) = (⟨j, hj⟩ : Fin k).succ := by ext; simp [hj]
  grind [intervalGapsWithin, intervalGapsWithin.fst]

中文:
定理 intervalGapsWithin_succ_fst_of_lt
  条件: (hj : j < k)
  证明: by
  have : (j.succ : Fin (k + 1)) = (⟨j, hj⟩ : Fin k).succ := by ext; simp [hj]
  grind [intervalGapsWithin, intervalGapsWithin.fst]

Depends on / 依赖: intervalGapsWithin, intervalGapsWithin.fst, j.succ
-/
theorem intervalGapsWithin_succ_fst_of_lt (hj : j < k) :
    (F.intervalGapsWithin h a b (j.succ)).1 = (F.orderEmbOfFin (α := α ×ₗ α) h ⟨j, hj⟩).2 := by
  have : (j.succ : Fin (k + 1)) = (⟨j, hj⟩ : Fin k).succ := by ext; simp [hj]
  grind [intervalGapsWithin, intervalGapsWithin.fst]

/--
theorem `intervalGapsWithin_fst_of_lt_lt` / 定理 `intervalGapsWithin_fst_of_lt_lt`

English:
theorem intervalGapsWithin_fst_of_lt_lt
  given: (hj₁ : 0 < j) (hj₂ : j - 1 < k)
  proof: by
  convert! F.intervalGapsWithin_succ_fst_of_lt h a b (j - 1) hj₂
  omega

@[simp]

中文:
定理 intervalGapsWithin_fst_of_lt_lt
  条件: (hj₁ : 0 < j) (hj₂ : j - 1 < k)
  证明: by
  convert! F.intervalGapsWithin_succ_fst_of_lt h a b (j - 1) hj₂
  omega

@[simp]

Depends on / 依赖: F.intervalGapsWithin_succ_fst_of_lt, convert, intervalGapsWithin_succ_fst_of_lt
-/
theorem intervalGapsWithin_fst_of_lt_lt (hj₁ : 0 < j) (hj₂ : j - 1 < k) :
    (F.intervalGapsWithin h a b j).1 = (F.orderEmbOfFin (α := α ×ₗ α) h ⟨j - 1, hj₂⟩).2 := by
  convert! F.intervalGapsWithin_succ_fst_of_lt h a b (j - 1) hj₂
  omega

@[simp]
/--
theorem `intervalGapsWithin_last_snd` / 定理 `intervalGapsWithin_last_snd`

English:
theorem intervalGapsWithin_last_snd
  statement: (F.intervalGapsWithin h a b (last k)).2 = b
  proof: by
  simp [intervalGapsWithin, intervalGapsWithin.snd]

中文:
定理 intervalGapsWithin_last_snd
  结论: (F.intervalGapsWithin h a b (last k)).2 = b
  证明: by
  simp [intervalGapsWithin, intervalGapsWithin.snd]

Depends on / 依赖: intervalGapsWithin, intervalGapsWithin.snd
-/
theorem intervalGapsWithin_last_snd : (F.intervalGapsWithin h a b (last k)).2 = b := by
  simp [intervalGapsWithin, intervalGapsWithin.snd]

/--
theorem `intervalGapsWithin_snd_of_lt` / 定理 `intervalGapsWithin_snd_of_lt`

English:
theorem intervalGapsWithin_snd_of_lt
  given: (hj : j < k)
  proof: by
  have : (j : Fin (k + 1)) != last k := by grind [val_cast_of_lt]
  simp only [intervalGapsWithin, intervalGapsWithin.snd, this, ↓reduceDIte]
  congr
  ext
  simp only [coe_castPred, val_natCast, Nat.mod_succ_eq_iff_lt]
  lia

中文:
定理 intervalGapsWithin_snd_of_lt
  条件: (hj : j < k)
  证明: by
  have : (j : Fin (k + 1)) != last k := by grind [val_cast_of_lt]
  simp only [intervalGapsWithin, intervalGapsWithin.snd, this, ↓reduceDIte]
  congr
  ext
  simp only [coe_castPred, val_natCast, Nat.mod_succ_eq_iff_lt]
  lia

Depends on / 依赖: Nat.mod_succ_eq_iff_lt, coe_castPred, intervalGapsWithin, intervalGapsWithin.snd, mod_succ_eq_iff_lt, reduceDIte, val_cast_of_lt, val_natCast
-/
theorem intervalGapsWithin_snd_of_lt (hj : j < k) :
    (F.intervalGapsWithin h a b j).2 = (F.orderEmbOfFin (α := α ×ₗ α) h ⟨j, hj⟩).1 := by
  have : (j : Fin (k + 1)) != last k := by grind [val_cast_of_lt]
  simp only [intervalGapsWithin, intervalGapsWithin.snd, this, ↓reduceDIte]
  congr
  ext
  simp only [coe_castPred, val_natCast, Nat.mod_succ_eq_iff_lt]
  lia

/--
theorem `intervalGapsWithin_mapsTo` / 定理 `intervalGapsWithin_mapsTo`

English:
theorem intervalGapsWithin_mapsTo
  statement: (Set.Iio k).MapsTo
  proof: by
  intro j hj
  rw [mem_Iio] at hj
  simp only [intervalGapsWithin_snd_of_lt, intervalGapsWithin_succ_fst_of_lt,
    SetLike.mem_coe, hj]
  convert! F.orderEmbOfFin_mem h ⟨j, hj⟩ using 1

中文:
定理 intervalGapsWithin_mapsTo
  结论: (集合.左无界右开区间 k).映射到
  证明: by
  intro j hj
  rw [mem_Iio] at hj
  simp only [intervalGapsWithin_snd_of_lt, intervalGapsWithin_succ_fst_of_lt,
    SetLike.mem_coe, hj]
  convert! F.orderEmbOfFin_mem h ⟨j, hj⟩ using 1

Depends on / 依赖: F.orderEmbOfFin_mem, SetLike, SetLike.mem_coe, convert, intervalGapsWithin_snd_of_lt, intervalGapsWithin_succ_fst_of_lt, mem_Iio, mem_coe, orderEmbOfFin_mem
-/
theorem intervalGapsWithin_mapsTo : (Set.Iio k).MapsTo
    (fun (j : Nat) => ((F.intervalGapsWithin h a b j).2, (F.intervalGapsWithin h a b j.succ).1))
    F := by
  intro j hj
  rw [mem_Iio] at hj
  simp only [intervalGapsWithin_snd_of_lt, intervalGapsWithin_succ_fst_of_lt,
    SetLike.mem_coe, hj]
  convert! F.orderEmbOfFin_mem h ⟨j, hj⟩ using 1

/--
theorem `intervalGapsWithin_injOn` / 定理 `intervalGapsWithin_injOn`

English:
theorem intervalGapsWithin_injOn
  statement: (Set.Iio k).InjOn
  proof: by
  intro j hj j' hj' hjj'
  rw [mem_Iio] at hj hj'
  simp only [hj, hj', intervalGapsWithin_snd_of_lt, intervalGapsWithin_succ_fst_of_lt] at hjj'
  grind [F.orderEmbOfFin (α := α ×ₗ α) h |>.injective hjj']

中文:
定理 intervalGapsWithin_injOn
  结论: (集合.左无界右开区间 k).单射限制
  证明: by
  intro j hj j' hj' hjj'
  rw [mem_Iio] at hj hj'
  simp only [hj, hj', intervalGapsWithin_snd_of_lt, intervalGapsWithin_succ_fst_of_lt] at hjj'
  grind [F.orderEmbOfFin (α := α ×ₗ α) h |>.injective hjj']

Depends on / 依赖: F.orderEmbOfFin, injective, intervalGapsWithin_snd_of_lt, intervalGapsWithin_succ_fst_of_lt, mem_Iio, orderEmbOfFin
-/
theorem intervalGapsWithin_injOn : (Set.Iio k).InjOn
    (fun (j : Nat) => ((F.intervalGapsWithin h a b j).2, (F.intervalGapsWithin h a b j.succ).1)) := by
  intro j hj j' hj' hjj'
  rw [mem_Iio] at hj hj'
  simp only [hj, hj', intervalGapsWithin_snd_of_lt, intervalGapsWithin_succ_fst_of_lt] at hjj'
  grind [F.orderEmbOfFin (α := α ×ₗ α) h |>.injective hjj']

set_option backward.isDefEq.respectTransparency false in
/--
theorem `intervalGapsWithin_surjOn` / 定理 `intervalGapsWithin_surjOn`

English:
theorem intervalGapsWithin_surjOn
  statement: (Set.Iio k).SurjOn
  proof: by
  intro z hz
  rw [← F.range_orderEmbOfFin h (α := α ×ₗ α)] at hz
  obtain ⟨j, hj⟩ := hz
  use j.val, j.prop
  simp [intervalGapsWithin_snd_of_lt, intervalGapsWithin_succ_fst_of_lt, j.prop, hj,
    -coe_eq_castSucc]

中文:
定理 intervalGapsWithin_surjOn
  结论: (集合.左无界右开区间 k).满射限制
  证明: by
  intro z hz
  rw [← F.range_orderEmbOfFin h (α := α ×ₗ α)] at hz
  obtain ⟨j, hj⟩ := hz
  use j.val, j.prop
  simp [intervalGapsWithin_snd_of_lt, intervalGapsWithin_succ_fst_of_lt, j.prop, hj,
    -coe_eq_castSucc]

Depends on / 依赖: F.range_orderEmbOfFin, coe_eq_castSucc, intervalGapsWithin_snd_of_lt, intervalGapsWithin_succ_fst_of_lt, j.prop, j.val, range_orderEmbOfFin
-/
theorem intervalGapsWithin_surjOn : (Set.Iio k).SurjOn
    (fun (j : Nat) => ((F.intervalGapsWithin h a b j).2, (F.intervalGapsWithin h a b j.succ).1))
    F := by
  intro z hz
  rw [← F.range_orderEmbOfFin h (α := α ×ₗ α)] at hz
  obtain ⟨j, hj⟩ := hz
  use j.val, j.prop
  simp [intervalGapsWithin_snd_of_lt, intervalGapsWithin_succ_fst_of_lt, j.prop, hj,
    -coe_eq_castSucc]

/--
theorem `intervalGapsWithin_le_fst` / 定理 `intervalGapsWithin_le_fst`

English:
theorem intervalGapsWithin_le_fst
  given: {a b : α} (hFab : forall ⦃z⦄, z in F -> a <= z.1 ∧ z.1 <= z.2 ∧ z.2 <= b)
  proof: by
  wlog hj : j < k + 1 generalizing j
  · grind [cast_val_eq_self]
  by_cases hj : j = 0
  · simp [hj]
  · have := hFab (F.intervalGapsWithin_mapsTo h a b (x := j - 1) (by grind))
    have hj₀ : j - 1 + 1 = j := by lia
    simp only [Nat.succ_eq_add_one, hj₀] at this
    grind

中文:
定理 intervalGapsWithin_le_fst
  条件: {a b : α} (hFab : 对任意 ⦃z⦄, z in F -> a <= z.1 ∧ z.1 <= z.2 ∧ z.2 <= b)
  证明: by
  wlog hj : j < k + 1 generalizing j
  · grind [cast_val_eq_self]
  by_cases hj : j = 0
  · simp [hj]
  · have := hFab (F.intervalGapsWithin_mapsTo h a b (x := j - 1) (by grind))
    have hj₀ : j - 1 + 1 = j := by lia
    simp only [Nat.succ_eq_add_one, hj₀] at this
    grind

Depends on / 依赖: F.intervalGapsWithin_mapsTo, Nat.succ_eq_add_one, cast_val_eq_self, generalizing, intervalGapsWithin_mapsTo, succ_eq_add_one
-/
theorem intervalGapsWithin_le_fst {a b : α} (hFab : forall ⦃z⦄, z in F -> a <= z.1 ∧ z.1 <= z.2 ∧ z.2 <= b) :
    a <= (F.intervalGapsWithin h a b j).1 := by
  wlog hj : j < k + 1 generalizing j
  · grind [cast_val_eq_self]
  by_cases hj : j = 0
  · simp [hj]
  · have := hFab (F.intervalGapsWithin_mapsTo h a b (x := j - 1) (by grind))
    have hj₀ : j - 1 + 1 = j := by lia
    simp only [Nat.succ_eq_add_one, hj₀] at this
    grind

/--
theorem `intervalGapsWithin_snd_le` / 定理 `intervalGapsWithin_snd_le`

English:
theorem intervalGapsWithin_snd_le
  given: {a b : α} (hFab : forall ⦃z⦄, z in F -> a <= z.1 ∧ z.1 <= z.2 ∧ z.2 <= b)
  proof: by
  wlog hj : j < k + 1 generalizing j
  · grind [cast_val_eq_self]
  by_cases hj : j = k
  · simp [hj]
  · have := hFab (F.intervalGapsWithin_mapsTo h a b (x := j) (by grind))
    grind

中文:
定理 intervalGapsWithin_snd_le
  条件: {a b : α} (hFab : 对任意 ⦃z⦄, z in F -> a <= z.1 ∧ z.1 <= z.2 ∧ z.2 <= b)
  证明: by
  wlog hj : j < k + 1 generalizing j
  · grind [cast_val_eq_self]
  by_cases hj : j = k
  · simp [hj]
  · have := hFab (F.intervalGapsWithin_mapsTo h a b (x := j) (by grind))
    grind

Depends on / 依赖: F.intervalGapsWithin_mapsTo, cast_val_eq_self, generalizing, intervalGapsWithin_mapsTo
-/
theorem intervalGapsWithin_snd_le {a b : α} (hFab : forall ⦃z⦄, z in F -> a <= z.1 ∧ z.1 <= z.2 ∧ z.2 <= b) :
    (F.intervalGapsWithin h a b j).2 <= b := by
  wlog hj : j < k + 1 generalizing j
  · grind [cast_val_eq_self]
  by_cases hj : j = k
  · simp [hj]
  · have := hFab (F.intervalGapsWithin_mapsTo h a b (x := j) (by grind))
    grind

set_option backward.isDefEq.respectTransparency false in
/--
theorem `intervalGapsWithin_fst_le_snd` / 定理 `intervalGapsWithin_fst_le_snd`

English:
theorem intervalGapsWithin_fst_le_snd
  statement: {a b : α} (hab : a <= b)
  proof: by
  wlog hj : j < k + 1 generalizing j
  · convert! this (j : Fin (k + 1)) (by grind) using 3 <;> grind [cast_val_eq_self]
  by_cases hj₁ : j = 0
  · simp only [hj₁]
    by_cases hk : 0 = k
    · simp only [natCast_zero, intervalGapsWithin_zero_fst]
      simp [show 0 = last k by grind, hab]
.left 

中文:
定理 intervalGapsWithin_fst_le_snd
  结论: {a b : α} (hab : a <= b)
  证明: by
  wlog hj : j < k + 1 generalizing j
  · convert! this (j : Fin (k + 1)) (by grind) using 3 <;> grind [cast_val_eq_self]
  by_cases hj₁ : j = 0
  · simp only [hj₁]
    by_cases hk : 0 = k
    · simp only [natCast_zero, intervalGapsWithin_zero_fst]
      simp [show 0 = last k by grind, hab]
.left 

Depends on / 依赖: F.intervalGapsWithin_mapsTo, cast_val_eq_self, convert, ge_iff_le, generalizing, intervalGapsWithin_last_snd, intervalGapsWithin_mapsTo, intervalGapsWithin_zero_fst, natCast_eq_last, natCast_zero, right.right
-/
theorem intervalGapsWithin_fst_le_snd {a b : α} (hab : a <= b)
    (hFab : forall ⦃z⦄, z in F -> a <= z.1 ∧ z.1 <= z.2 ∧ z.2 <= b)
    (hF : (SetLike.coe F).PairwiseDisjoint (fun z => Set.Icc z.1 z.2)) :
    (F.intervalGapsWithin h a b j).1 <= (F.intervalGapsWithin h a b j).2 := by
  wlog hj : j < k + 1 generalizing j
  · convert! this (j : Fin (k + 1)) (by grind) using 3 <;> grind [cast_val_eq_self]
  by_cases hj₁ : j = 0
  · simp only [hj₁]
    by_cases hk : 0 = k
    · simp only [natCast_zero, intervalGapsWithin_zero_fst]
      simp [show 0 = last k by grind, hab]
.left · exact hFab (F.intervalGapsWithin_mapsTo h a b (x := 0) (by grind))
  have hk : k - 1 + 1 = k := by omega
  by_cases hj₂ : j = k
  · simp only [hj₂, natCast_eq_last, intervalGapsWithin_last_snd, ge_iff_le]
.right.right using 1 convert! hFab (F.intervalGapsWithin_mapsTo h a b (x := j - 1) (by grind))
    simp [hj₂, hk]
  rw [intervalGapsWithin_fst_of_lt_lt (hj₁ := by omega) (hj₂ := by omega)]; rw [intervalGapsWithin_snd_of_lt (hj := by omega)]
  have hj₃ : (⟨j - 1, by omega⟩ : Fin k) != ⟨j, by omega⟩ := by grind
  set G := F.orderEmbOfFin (α := α ×ₗ α) h
  have := hF (by simp [G, F.orderEmbOfFin_mem (α := α ×ₗ α)])
    (by simp [G, F.orderEmbOfFin_mem (α := α ×ₗ α)]) (G.injective.ne (hj₃))
  contrapose! this
  simp only [Set.not_disjoint_iff, Set.mem_Icc]
  use (G ⟨j, by omega⟩).1
  have hG : (G ⟨j - 1, by omega⟩).1 <= (G ⟨j, by omega⟩).1 :=
.left Prod.Lex.le_iff'.mp (G.monotone (by simp [le_iff_val_le_val]))
  have hFabi := hFab (z := G ⟨j, by omega⟩) (by simp [G, F.orderEmbOfFin_mem (α := α ×ₗ α)])
  simp [hFabi, this.le, hG]

/--
theorem `intervalGapsWithin_pairwiseDisjoint_Ioc` / 定理 `intervalGapsWithin_pairwiseDisjoint_Ioc`

English:
theorem intervalGapsWithin_pairwiseDisjoint_Ioc
  statement: {a b : α}
  proof: by
  intro j hj j' hj' hjj'
  rw [mem_Iio] at hj hj'
  wlog hij' : j < j' generalizing j j'
  · exact (this hj' hj hjj'.symm (by omega)).symm
  rw [Function.onFun]; rw [Set.disjoint_iff_inter_eq_empty]
  suffices (F.intervalGapsWithin h a b j).2 <= (F.intervalGapsWithin h a b j').1 by grind
  have h

中文:
定理 intervalGapsWithin_pairwiseDisjoint_Ioc
  结论: {a b : α}
  证明: by
  intro j hj j' hj' hjj'
  rw [mem_Iio] at hj hj'
  wlog hij' : j < j' generalizing j j'
  · exact (this hj' hj hjj'.symm (by omega)).symm
  rw [Function.onFun]; rw [Set.disjoint_iff_inter_eq_empty]
  suffices (F.intervalGapsWithin h a b j).2 <= (F.intervalGapsWithin h a b j').1 by grind
  have h

Depends on / 依赖: F.intervalGapsWithin, F.intervalGapsWithin_mapsTo, Function, Function.onFun, Nat.succ_eq_add_one, Set.disjoint_iff_inter_eq_empty, disjoint_iff_inter_eq_empty, generalizing, intervalGapsWithin, intervalGapsWithin_mapsTo, intervalGapsWithin_snd_of_lt, mem_Iio, right.left, succ_eq_add_one
-/
theorem intervalGapsWithin_pairwiseDisjoint_Ioc {a b : α}
    (hFab : forall ⦃z⦄, z in F -> a <= z.1 ∧ z.1 <= z.2 ∧ z.2 <= b) :
    (Set.Iio (k + 1)).PairwiseDisjoint (fun (j : Nat) =>
      Set.Ioc (F.intervalGapsWithin h a b j).1 (F.intervalGapsWithin h a b j).2) := by
  intro j hj j' hj' hjj'
  rw [mem_Iio] at hj hj'
  wlog hij' : j < j' generalizing j j'
  · exact (this hj' hj hjj'.symm (by omega)).symm
  rw [Function.onFun]; rw [Set.disjoint_iff_inter_eq_empty]
  suffices (F.intervalGapsWithin h a b j).2 <= (F.intervalGapsWithin h a b j').1 by grind
  have hj'₀ : j' - 1 + 1 = j' := by omega
.right.left have := hFab (F.intervalGapsWithin_mapsTo h a b (x := j' - 1) (by grind))
  simp only [Nat.succ_eq_add_one, hj'₀] at this
  grw [← this]
  rw [intervalGapsWithin_snd_of_lt (hj := by omega)]; rw [intervalGapsWithin_snd_of_lt (hj := by omega)]
.left exact Prod.Lex.le_iff'.mp (F.orderEmbOfFin (α := α ×ₗ α) h |>.monotone (by grind))

end Finset

end IntervalGapsWithin
