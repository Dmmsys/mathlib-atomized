/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Data.List.Lattice
public import Mathlib.Data.Bool.Basic
public import Mathlib.Order.Lattice

/-!
# Intervals in ℕ

This file defines intervals of naturals. `List.Ico m n` is the list of integers greater than `m`
and strictly less than `n`.

## TODO
- Define `Ioo` and `Icc`, state basic lemmas about them.
- Also do the versions for integers?
- One could generalise even further, defining 'locally finite partial orders', for which
  `Set.Ico a b` is `[Finite]`, and 'locally finite total orders', for which there is a list model.
- Once the above is done, get rid of `Int.range` (and maybe `List.range'`?).
-/

@[expose] public section


open Nat

namespace List

/--
Definition of `Ico` / `Ico` 的定义

English:
definition Ico
  signature: (n m : Nat)
  body: range' n (m - n)

中文:
定义 Ico
  签名: (n m : 自然数)
  定义体: range' n (m - n)
-/
def Ico (n m : Nat) : List Nat :=
  range' n (m - n)

namespace Ico

/--
theorem `zero_bot` / 定理 `zero_bot`

English:
theorem zero_bot
  given: (n : Nat)
  statement: Ico 0 n = range n
  proof: by rw [Ico, Nat.sub_zero, range_eq_range']

@[simp]

中文:
定理 zero_bot
  条件: (n : 自然数)
  结论: Ico 0 n = range n
  证明: by rw [Ico, Nat.sub_zero, range_eq_range']

@[simp]

Depends on / 依赖: Nat.sub_zero, range_eq_range, sub_zero
-/
theorem zero_bot (n : Nat) : Ico 0 n = range n := by rw [Ico, Nat.sub_zero, range_eq_range']

@[simp]
/--
theorem `length` / 定理 `length`

English:
theorem length
  given: (n m : Nat)
  statement: length (Ico n m) = m - n
  proof: by
  dsimp [Ico]
  simp [length_range']

中文:
定理 length
  条件: (n m : 自然数)
  结论: length (Ico n m) = m - n
  证明: by
  dsimp [Ico]
  simp [length_range']

Depends on / 依赖: length_range
-/
theorem length (n m : Nat) : length (Ico n m) = m - n := by
  dsimp [Ico]
  simp [length_range']

/--
theorem `pairwise_lt` / 定理 `pairwise_lt`

English:
theorem pairwise_lt
  given: (n m : Nat)
  statement: Pairwise (· < ·) (Ico n m)
  proof: by
  dsimp [Ico]
  simp [pairwise_lt_range']

中文:
定理 pairwise_lt
  条件: (n m : 自然数)
  结论: Pairwise (· < ·) (Ico n m)
  证明: by
  dsimp [Ico]
  simp [pairwise_lt_range']

Depends on / 依赖: pairwise_lt_range
-/
theorem pairwise_lt (n m : Nat) : Pairwise (· < ·) (Ico n m) := by
  dsimp [Ico]
  simp [pairwise_lt_range']

/--
theorem `nodup` / 定理 `nodup`

English:
theorem nodup
  given: (n m : Nat)
  statement: Nodup (Ico n m)
  proof: by
  dsimp [Ico]
  simp [nodup_range']

@[simp]

中文:
定理 nodup
  条件: (n m : 自然数)
  结论: Nodup (Ico n m)
  证明: by
  dsimp [Ico]
  simp [nodup_range']

@[simp]

Depends on / 依赖: nodup_range
-/
theorem nodup (n m : Nat) : Nodup (Ico n m) := by
  dsimp [Ico]
  simp [nodup_range']

@[simp]
/--
theorem `mem` / 定理 `mem`

English:
theorem mem
  given: {n m l : Nat}
  statement: l in Ico n m ↔ n <= l ∧ l < m
  proof: by
  suffices n <= l ∧ l < n + (m - n) ↔ n <= l ∧ l < m by simp [Ico, this]
  lia

中文:
定理 mem
  条件: {n m l : 自然数}
  结论: l in Ico n m ↔ n <= l ∧ l < m
  证明: by
  suffices n <= l ∧ l < n + (m - n) ↔ n <= l ∧ l < m by simp [Ico, this]
  lia
-/
theorem mem {n m l : Nat} : l in Ico n m ↔ n <= l ∧ l < m := by
  suffices n <= l ∧ l < n + (m - n) ↔ n <= l ∧ l < m by simp [Ico, this]
  lia

/--
theorem `eq_nil_of_le` / 定理 `eq_nil_of_le`

English:
theorem eq_nil_of_le
  given: {n m : Nat} (h : m <= n)
  statement: Ico n m = []
  proof: by
  simp [Ico, Nat.sub_eq_zero_iff_le.mpr h]

中文:
定理 eq_nil_of_le
  条件: {n m : 自然数} (h : m <= n)
  结论: Ico n m = []
  证明: by
  simp [Ico, Nat.sub_eq_zero_iff_le.mpr h]

Depends on / 依赖: Nat.sub_eq_zero_iff_le.mpr, sub_eq_zero_iff_le
-/
theorem eq_nil_of_le {n m : Nat} (h : m <= n) : Ico n m = [] := by
  simp [Ico, Nat.sub_eq_zero_iff_le.mpr h]

/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  given: (n m k : Nat)
  statement: (Ico n m).map (k + ·) = Ico (n + k) (m + k)
  proof: by
  rw [Ico]; rw [Ico]; rw [map_add_range']; rw [Nat.add_sub_add_right m k]; rw [Nat.add_comm n k]

中文:
定理 map_add
  条件: (n m k : 自然数)
  结论: (Ico n m).map (k + ·) = Ico (n + k) (m + k)
  证明: by
  rw [Ico]; rw [Ico]; rw [map_add_range']; rw [Nat.add_sub_add_right m k]; rw [Nat.add_comm n k]

Depends on / 依赖: Nat.add_comm, Nat.add_sub_add_right, add_comm, add_sub_add_right, map_add_range
-/
theorem map_add (n m k : Nat) : (Ico n m).map (k + ·) = Ico (n + k) (m + k) := by
  rw [Ico]; rw [Ico]; rw [map_add_range']; rw [Nat.add_sub_add_right m k]; rw [Nat.add_comm n k]

/--
theorem `map_sub` / 定理 `map_sub`

English:
theorem map_sub
  given: (n m k : Nat) (h₁ : k <= n)
  proof: by
  rw [Ico]; rw [Ico]; rw [Nat.sub_sub_sub_cancel_right h₁]; rw [map_sub_range' h₁]

@[simp]

中文:
定理 map_sub
  条件: (n m k : 自然数) (h₁ : k <= n)
  证明: by
  rw [Ico]; rw [Ico]; rw [Nat.sub_sub_sub_cancel_right h₁]; rw [map_sub_range' h₁]

@[simp]

Depends on / 依赖: Nat.sub_sub_sub_cancel_right, map_sub_range, sub_sub_sub_cancel_right
-/
theorem map_sub (n m k : Nat) (h₁ : k <= n) :
    ((Ico n m).map fun x => x - k) = Ico (n - k) (m - k) := by
  rw [Ico]; rw [Ico]; rw [Nat.sub_sub_sub_cancel_right h₁]; rw [map_sub_range' h₁]

@[simp]
/--
theorem `self_empty` / 定理 `self_empty`

English:
theorem self_empty
  given: {n : Nat}
  statement: Ico n n = []
  proof: eq_nil_of_le (le_refl n)

@[simp]

中文:
定理 self_empty
  条件: {n : 自然数}
  结论: Ico n n = []
  证明: eq_nil_of_le (le_refl n)

@[simp]

Depends on / 依赖: eq_nil_of_le, le_refl
-/
theorem self_empty {n : Nat} : Ico n n = [] :=
  eq_nil_of_le (le_refl n)

@[simp]
/--
theorem `eq_empty_iff` / 定理 `eq_empty_iff`

English:
theorem eq_empty_iff
  given: {n m : Nat}
  statement: Ico n m = [] ↔ m <= n
  proof: Iff.intro (fun h => Nat.sub_eq_zero_iff_le.mp <| by rw [← length, h, List.length]) eq_nil_of_le

中文:
定理 eq_empty_iff
  条件: {n m : 自然数}
  结论: Ico n m = [] ↔ m <= n
  证明: Iff.intro (fun h => Nat.sub_eq_zero_iff_le.mp <| by rw [← length, h, List.length]) eq_nil_of_le

Depends on / 依赖: Iff.intro, List.length, Nat.sub_eq_zero_iff_le.mp, eq_nil_of_le, length, sub_eq_zero_iff_le
-/
theorem eq_empty_iff {n m : Nat} : Ico n m = [] ↔ m <= n :=
  Iff.intro (fun h => Nat.sub_eq_zero_iff_le.mp <| by rw [← length, h, List.length]) eq_nil_of_le

/--
theorem `append_consecutive` / 定理 `append_consecutive`

English:
theorem append_consecutive
  given: {n m l : Nat} (hnm : n <= m) (hml : m <= l)
  proof: by
  dsimp only [Ico]
  convert! range'_append using 2
  · rw [Nat.one_mul, Nat.add_sub_cancel' hnm]
  · lia

@[simp]

中文:
定理 append_consecutive
  条件: {n m l : 自然数} (hnm : n <= m) (hml : m <= l)
  证明: by
  dsimp only [Ico]
  convert! range'_append using 2
  · rw [Nat.one_mul, Nat.add_sub_cancel' hnm]
  · lia

@[simp]

Depends on / 依赖: Nat.add_sub_cancel, Nat.one_mul, _append, add_sub_cancel, convert, one_mul
-/
theorem append_consecutive {n m l : Nat} (hnm : n <= m) (hml : m <= l) :
    Ico n m ++ Ico m l = Ico n l := by
  dsimp only [Ico]
  convert! range'_append using 2
  · rw [Nat.one_mul, Nat.add_sub_cancel' hnm]
  · lia

@[simp]
/--
theorem `inter_consecutive` / 定理 `inter_consecutive`

English:
theorem inter_consecutive
  given: (n m l : Nat)
  statement: Ico n m inter Ico m l = []
  proof: by
  apply eq_nil_iff_forall_not_mem.2
  intro a
  simp only [and_imp, not_and, not_lt, List.mem_inter_iff, List.Ico.mem]
  intro _ h₂ h₃
  exfalso
  exact not_lt_of_ge h₃ h₂

@[simp]

中文:
定理 inter_consecutive
  条件: (n m l : 自然数)
  结论: Ico n m inter Ico m l = []
  证明: by
  apply eq_nil_iff_forall_not_mem.2
  intro a
  simp only [and_imp, not_and, not_lt, List.mem_inter_iff, List.Ico.mem]
  intro _ h₂ h₃
  exfalso
  exact not_lt_of_ge h₃ h₂

@[simp]

Depends on / 依赖: List.Ico.mem, List.mem_inter_iff, and_imp, eq_nil_iff_forall_not_mem, mem_inter_iff, not_and, not_lt, not_lt_of_ge
-/
theorem inter_consecutive (n m l : Nat) : Ico n m inter Ico m l = [] := by
  apply eq_nil_iff_forall_not_mem.2
  intro a
  simp only [and_imp, not_and, not_lt, List.mem_inter_iff, List.Ico.mem]
  intro _ h₂ h₃
  exfalso
  exact not_lt_of_ge h₃ h₂

@[simp]
/--
theorem `bagInter_consecutive` / 定理 `bagInter_consecutive`

English:
theorem bagInter_consecutive
  given: (n m l : Nat)
  proof: (bagInter_nil_iff_inter_nil _ _).2 (by convert! inter_consecutive n m l)

@[simp]

中文:
定理 bagInter_consecutive
  条件: (n m l : 自然数)
  证明: (bagInter_nil_iff_inter_nil _ _).2 (by convert! inter_consecutive n m l)

@[simp]

Depends on / 依赖: bagInter_nil_iff_inter_nil, convert, inter_consecutive
-/
theorem bagInter_consecutive (n m l : Nat) :
    @List.bagInter Nat instBEqOfDecidableEq (Ico n m) (Ico m l) = [] :=
  (bagInter_nil_iff_inter_nil _ _).2 (by convert! inter_consecutive n m l)

@[simp]
/--
theorem `succ_singleton` / 定理 `succ_singleton`

English:
theorem succ_singleton
  given: {n : Nat}
  statement: Ico n (n + 1) = [n]
  proof: by
  dsimp [Ico]
  simp [Nat.add_sub_cancel_left]

中文:
定理 succ_singleton
  条件: {n : 自然数}
  结论: Ico n (n + 1) = [n]
  证明: by
  dsimp [Ico]
  simp [Nat.add_sub_cancel_left]

Depends on / 依赖: Nat.add_sub_cancel_left, add_sub_cancel_left
-/
theorem succ_singleton {n : Nat} : Ico n (n + 1) = [n] := by
  dsimp [Ico]
  simp [Nat.add_sub_cancel_left]

/--
theorem `succ_top` / 定理 `succ_top`

English:
theorem succ_top
  given: {n m : Nat} (h : n <= m)
  statement: Ico n (m + 1) = Ico n m ++ [m]
  proof: by
  rwa [← succ_singleton, append_consecutive]
  exact Nat.le_succ _

中文:
定理 succ_top
  条件: {n m : 自然数} (h : n <= m)
  结论: Ico n (m + 1) = Ico n m ++ [m]
  证明: by
  rwa [← succ_singleton, append_consecutive]
  exact Nat.le_succ _

Depends on / 依赖: Nat.le_succ, append_consecutive, le_succ, succ_singleton
-/
theorem succ_top {n m : Nat} (h : n <= m) : Ico n (m + 1) = Ico n m ++ [m] := by
  rwa [← succ_singleton, append_consecutive]
  exact Nat.le_succ _

/--
theorem `eq_cons` / 定理 `eq_cons`

English:
theorem eq_cons
  given: {n m : Nat} (h : n < m)
  statement: Ico n m = n :: Ico (n + 1) m
  proof: by
  rw [← append_consecutive (Nat.le_succ n) h]; rw [succ_singleton]
  rfl

@[simp]

中文:
定理 eq_cons
  条件: {n m : 自然数} (h : n < m)
  结论: Ico n m = n :: Ico (n + 1) m
  证明: by
  rw [← append_consecutive (Nat.le_succ n) h]; rw [succ_singleton]
  rfl

@[simp]

Depends on / 依赖: Nat.le_succ, append_consecutive, le_succ, succ_singleton
-/
theorem eq_cons {n m : Nat} (h : n < m) : Ico n m = n :: Ico (n + 1) m := by
  rw [← append_consecutive (Nat.le_succ n) h]; rw [succ_singleton]
  rfl

@[simp]
/--
theorem `pred_singleton` / 定理 `pred_singleton`

English:
theorem pred_singleton
  given: {m : Nat} (h : 0 < m)
  statement: Ico (m - 1) m = [m - 1]
  proof: by
  simp [Ico, Nat.sub_sub_self (succ_le_of_lt h)]

中文:
定理 pred_singleton
  条件: {m : 自然数} (h : 0 < m)
  结论: Ico (m - 1) m = [m - 1]
  证明: by
  simp [Ico, Nat.sub_sub_self (succ_le_of_lt h)]

Depends on / 依赖: Nat.sub_sub_self, sub_sub_self, succ_le_of_lt
-/
theorem pred_singleton {m : Nat} (h : 0 < m) : Ico (m - 1) m = [m - 1] := by
  simp [Ico, Nat.sub_sub_self (succ_le_of_lt h)]

/--
theorem `isChain_succ` / 定理 `isChain_succ`

English:
theorem isChain_succ
  given: (n m : Nat)
  statement: IsChain (fun a b => b = succ a) (Ico n m)
  proof: by
  by_cases! h : n < m
  · rw [eq_cons h]
    unfold List.Ico
    exact isChain_range' _ (_ + 1) 1
  · rw [eq_nil_of_le h]
    exact .nil

中文:
定理 isChain_succ
  条件: (n m : 自然数)
  结论: IsChain (fun a b => b = succ a) (Ico n m)
  证明: by
  by_cases! h : n < m
  · rw [eq_cons h]
    unfold List.Ico
    exact isChain_range' _ (_ + 1) 1
  · rw [eq_nil_of_le h]
    exact .nil

Depends on / 依赖: List.Ico, eq_cons, eq_nil_of_le, isChain_range
-/
theorem isChain_succ (n m : Nat) : IsChain (fun a b => b = succ a) (Ico n m) := by
  by_cases! h : n < m
  · rw [eq_cons h]
    unfold List.Ico
    exact isChain_range' _ (_ + 1) 1
  · rw [eq_nil_of_le h]
    exact .nil

/--
theorem `notMem_top` / 定理 `notMem_top`

English:
theorem notMem_top
  given: {n m : Nat}
  statement: m ∉ Ico n m
  proof: by simp

中文:
定理 notMem_top
  条件: {n m : 自然数}
  结论: m ∉ Ico n m
  证明: by simp
-/
theorem notMem_top {n m : Nat} : m ∉ Ico n m := by simp

/--
theorem `filter_lt_of_top_le` / 定理 `filter_lt_of_top_le`

English:
theorem filter_lt_of_top_le
  given: {n m l : Nat} (hml : m <= l)
  proof: filter_eq_self.2 fun k hk => by
    simp only [(lt_of_lt_of_le (mem.1 hk).2 hml), decide_true]

中文:
定理 filter_lt_of_top_le
  条件: {n m l : 自然数} (hml : m <= l)
  证明: filter_eq_self.2 fun k hk => by
    simp only [(lt_of_lt_of_le (mem.1 hk).2 hml), decide_true]

Depends on / 依赖: decide_true, filter_eq_self, lt_of_lt_of_le
-/
theorem filter_lt_of_top_le {n m l : Nat} (hml : m <= l) :
    ((Ico n m).filter fun x => x < l) = Ico n m :=
  filter_eq_self.2 fun k hk => by
    simp only [(lt_of_lt_of_le (mem.1 hk).2 hml), decide_true]

/--
theorem `filter_lt_of_le_bot` / 定理 `filter_lt_of_le_bot`

English:
theorem filter_lt_of_le_bot
  given: {n m l : Nat} (hln : l <= n)
  statement: ((Ico n m).filter fun x => x < l) = []
  proof: filter_eq_nil_iff.2 fun k hk => by
     simp only [decide_eq_true_eq, not_lt]
     apply le_trans hln
     exact (mem.1 hk).1

中文:
定理 filter_lt_of_le_bot
  条件: {n m l : 自然数} (hln : l <= n)
  结论: ((Ico n m).filter fun x => x < l) = []
  证明: filter_eq_nil_iff.2 fun k hk => by
     simp only [decide_eq_true_eq, not_lt]
     apply le_trans hln
     exact (mem.1 hk).1

Depends on / 依赖: decide_eq_true_eq, filter_eq_nil_iff, le_trans, not_lt
-/
theorem filter_lt_of_le_bot {n m l : Nat} (hln : l <= n) : ((Ico n m).filter fun x => x < l) = [] :=
  filter_eq_nil_iff.2 fun k hk => by
     simp only [decide_eq_true_eq, not_lt]
     apply le_trans hln
     exact (mem.1 hk).1

/--
theorem `filter_lt_of_ge` / 定理 `filter_lt_of_ge`

English:
theorem filter_lt_of_ge
  given: {n m l : Nat} (hlm : l <= m)
  proof: by
  rcases le_total n l with hnl | hln
  · rw [← append_consecutive hnl hlm, filter_append, filter_lt_of_top_le (le_refl l),
      filter_lt_of_le_bot (le_refl l), append_nil]
  · rw [eq_nil_of_le hln, filter_lt_of_le_bot hln]

@[simp]

中文:
定理 filter_lt_of_ge
  条件: {n m l : 自然数} (hlm : l <= m)
  证明: by
  rcases le_total n l with hnl | hln
  · rw [← append_consecutive hnl hlm, filter_append, filter_lt_of_top_le (le_refl l),
      filter_lt_of_le_bot (le_refl l), append_nil]
  · rw [eq_nil_of_le hln, filter_lt_of_le_bot hln]

@[simp]

Depends on / 依赖: append_consecutive, append_nil, eq_nil_of_le, filter_append, filter_lt_of_le_bot, filter_lt_of_top_le, le_refl, le_total
-/
theorem filter_lt_of_ge {n m l : Nat} (hlm : l <= m) :
    ((Ico n m).filter fun x => x < l) = Ico n l := by
  rcases le_total n l with hnl | hln
  · rw [← append_consecutive hnl hlm, filter_append, filter_lt_of_top_le (le_refl l),
      filter_lt_of_le_bot (le_refl l), append_nil]
  · rw [eq_nil_of_le hln, filter_lt_of_le_bot hln]

@[simp]
/--
theorem `filter_lt` / 定理 `filter_lt`

English:
theorem filter_lt
  given: (n m l : Nat)
  proof: by
  rcases le_total m l with hml | hlm
  · rw [min_eq_left hml, filter_lt_of_top_le hml]
  · rw [min_eq_right hlm, filter_lt_of_ge hlm]

中文:
定理 filter_lt
  条件: (n m l : 自然数)
  证明: by
  rcases le_total m l with hml | hlm
  · rw [min_eq_left hml, filter_lt_of_top_le hml]
  · rw [min_eq_right hlm, filter_lt_of_ge hlm]

Depends on / 依赖: filter_lt_of_ge, filter_lt_of_top_le, le_total, min_eq_left, min_eq_right
-/
theorem filter_lt (n m l : Nat) :
    ((Ico n m).filter fun x => x < l) = Ico n (min m l) := by
  rcases le_total m l with hml | hlm
  · rw [min_eq_left hml, filter_lt_of_top_le hml]
  · rw [min_eq_right hlm, filter_lt_of_ge hlm]

/--
theorem `filter_le_of_le_bot` / 定理 `filter_le_of_le_bot`

English:
theorem filter_le_of_le_bot
  given: {n m l : Nat} (hln : l <= n)
  proof: filter_eq_self.2 fun k hk => by
    rw [decide_eq_true_eq]
    exact le_trans hln (mem.1 hk).1

中文:
定理 filter_le_of_le_bot
  条件: {n m l : 自然数} (hln : l <= n)
  证明: filter_eq_self.2 fun k hk => by
    rw [decide_eq_true_eq]
    exact le_trans hln (mem.1 hk).1

Depends on / 依赖: decide_eq_true_eq, filter_eq_self, le_trans
-/
theorem filter_le_of_le_bot {n m l : Nat} (hln : l <= n) :
    ((Ico n m).filter fun x => l <= x) = Ico n m :=
  filter_eq_self.2 fun k hk => by
    rw [decide_eq_true_eq]
    exact le_trans hln (mem.1 hk).1

/--
theorem `filter_le_of_top_le` / 定理 `filter_le_of_top_le`

English:
theorem filter_le_of_top_le
  given: {n m l : Nat} (hml : m <= l)
  statement: ((Ico n m).filter fun x => l <= x) = []
  proof: filter_eq_nil_iff.2 fun k hk => by
    rw [decide_eq_true_eq]
    exact not_le_of_gt (lt_of_lt_of_le (mem.1 hk).2 hml)

中文:
定理 filter_le_of_top_le
  条件: {n m l : 自然数} (hml : m <= l)
  结论: ((Ico n m).filter fun x => l <= x) = []
  证明: filter_eq_nil_iff.2 fun k hk => by
    rw [decide_eq_true_eq]
    exact not_le_of_gt (lt_of_lt_of_le (mem.1 hk).2 hml)

Depends on / 依赖: decide_eq_true_eq, filter_eq_nil_iff, lt_of_lt_of_le, not_le_of_gt
-/
theorem filter_le_of_top_le {n m l : Nat} (hml : m <= l) : ((Ico n m).filter fun x => l <= x) = [] :=
  filter_eq_nil_iff.2 fun k hk => by
    rw [decide_eq_true_eq]
    exact not_le_of_gt (lt_of_lt_of_le (mem.1 hk).2 hml)

/--
theorem `filter_le_of_le` / 定理 `filter_le_of_le`

English:
theorem filter_le_of_le
  given: {n m l : Nat} (hnl : n <= l)
  proof: by
  rcases le_total l m with hlm | hml
  · rw [← append_consecutive hnl hlm, filter_append, filter_le_of_top_le (le_refl l),
      filter_le_of_le_bot (le_refl l), nil_append]
  · rw [eq_nil_of_le hml, filter_le_of_top_le hml]

@[simp]

中文:
定理 filter_le_of_le
  条件: {n m l : 自然数} (hnl : n <= l)
  证明: by
  rcases le_total l m with hlm | hml
  · rw [← append_consecutive hnl hlm, filter_append, filter_le_of_top_le (le_refl l),
      filter_le_of_le_bot (le_refl l), nil_append]
  · rw [eq_nil_of_le hml, filter_le_of_top_le hml]

@[simp]

Depends on / 依赖: append_consecutive, eq_nil_of_le, filter_append, filter_le_of_le_bot, filter_le_of_top_le, le_refl, le_total, nil_append
-/
theorem filter_le_of_le {n m l : Nat} (hnl : n <= l) :
    ((Ico n m).filter fun x => l <= x) = Ico l m := by
  rcases le_total l m with hlm | hml
  · rw [← append_consecutive hnl hlm, filter_append, filter_le_of_top_le (le_refl l),
      filter_le_of_le_bot (le_refl l), nil_append]
  · rw [eq_nil_of_le hml, filter_le_of_top_le hml]

@[simp]
/--
theorem `filter_le` / 定理 `filter_le`

English:
theorem filter_le
  given: (n m l : Nat)
  statement: ((Ico n m).filter fun x => l <= x) = Ico (max n l) m
  proof: by
  rcases le_total n l with hnl | hln
  · rw [max_eq_right hnl, filter_le_of_le hnl]
  · rw [max_eq_left hln, filter_le_of_le_bot hln]

中文:
定理 filter_le
  条件: (n m l : 自然数)
  结论: ((Ico n m).filter fun x => l <= x) = Ico (max n l) m
  证明: by
  rcases le_total n l with hnl | hln
  · rw [max_eq_right hnl, filter_le_of_le hnl]
  · rw [max_eq_left hln, filter_le_of_le_bot hln]

Depends on / 依赖: filter_le_of_le, filter_le_of_le_bot, le_total, max_eq_left, max_eq_right
-/
theorem filter_le (n m l : Nat) : ((Ico n m).filter fun x => l <= x) = Ico (max n l) m := by
  rcases le_total n l with hnl | hln
  · rw [max_eq_right hnl, filter_le_of_le hnl]
  · rw [max_eq_left hln, filter_le_of_le_bot hln]

/--
theorem `filter_lt_of_succ_bot` / 定理 `filter_lt_of_succ_bot`

English:
theorem filter_lt_of_succ_bot
  given: {n m : Nat} (hnm : n < m)
  proof: by
  have r : min m (n + 1) = n + 1 := (@inf_eq_right _ _ m (n + 1)).mpr hnm
  simp [filter_lt n m (n + 1), r]

@[simp]

中文:
定理 filter_lt_of_succ_bot
  条件: {n m : 自然数} (hnm : n < m)
  证明: by
  have r : min m (n + 1) = n + 1 := (@inf_eq_right _ _ m (n + 1)).mpr hnm
  simp [filter_lt n m (n + 1), r]

@[simp]

Depends on / 依赖: filter_lt, inf_eq_right
-/
theorem filter_lt_of_succ_bot {n m : Nat} (hnm : n < m) :
    ((Ico n m).filter fun x => x < n + 1) = [n] := by
  have r : min m (n + 1) = n + 1 := (@inf_eq_right _ _ m (n + 1)).mpr hnm
  simp [filter_lt n m (n + 1), r]

@[simp]
/--
theorem `filter_le_of_bot` / 定理 `filter_le_of_bot`

English:
theorem filter_le_of_bot
  given: {n m : Nat} (hnm : n < m)
  statement: ((Ico n m).filter fun x => x <= n) = [n]
  proof: by
  rw [← filter_lt_of_succ_bot hnm]
  exact filter_congr fun _ _ => by
    simpa using Nat.lt_succ_iff.symm

中文:
定理 filter_le_of_bot
  条件: {n m : 自然数} (hnm : n < m)
  结论: ((Ico n m).filter fun x => x <= n) = [n]
  证明: by
  rw [← filter_lt_of_succ_bot hnm]
  exact filter_congr fun _ _ => by
    simpa using Nat.lt_succ_iff.symm

Depends on / 依赖: Nat.lt_succ_iff.symm, filter_congr, filter_lt_of_succ_bot, lt_succ_iff
-/
theorem filter_le_of_bot {n m : Nat} (hnm : n < m) : ((Ico n m).filter fun x => x <= n) = [n] := by
  rw [← filter_lt_of_succ_bot hnm]
  exact filter_congr fun _ _ => by
    simpa using Nat.lt_succ_iff.symm

/--
theorem `trichotomy` / 定理 `trichotomy`

English:
theorem trichotomy
  given: (n a b : Nat)
  statement: n < a ∨ b <= n ∨ n in Ico a b
  proof: by
  grind [mem]

中文:
定理 trichotomy
  条件: (n a b : 自然数)
  结论: n < a ∨ b <= n ∨ n in Ico a b
  证明: by
  grind [mem]
-/
theorem trichotomy (n a b : Nat) : n < a ∨ b <= n ∨ n in Ico a b := by
  grind [mem]

end Ico

end List
