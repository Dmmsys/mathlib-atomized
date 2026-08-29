/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
module

public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Set.Lattice
public import Mathlib.Order.Interval.Set.LinearOrder

/-!
# Extra lemmas about unions of intervals

This file contains lemmas about finite unions of intervals which can't be included with the lemmas
concerning infinite unions in `Mathlib/Order/Interval/Set/Disjoint.lean` because we use
`Finset.range`.
-/

public section

open Set

/--
theorem `Ioc_subset_biUnion_Ioc` / 定理 `Ioc_subset_biUnion_Ioc`

English:
theorem Ioc_subset_biUnion_Ioc
  given: {X : Type*} [LinearOrder X] (N : Nat) (a : Nat -> X)
  proof: by
  induction N with
  | zero => simp
  | succ N ih => calc
    _ subseteq Ioc (a 0) (a N) union Ioc (a N) (a (N + 1)) := Ioc_subset_Ioc_union_Ioc
    _ subseteq _ := by simpa [Finset.range_add_one] using
                  union_subset_union_right (Ioc (a N) (a (N + 1))) ih

中文:
定理 Ioc_subset_biUnion_Ioc
  条件: {X : 类型} [线性序 X] (N : 自然数) (a : 自然数 -> X)
  证明: by
  induction N with
  | zero => simp
  | succ N ih => calc
    _ subseteq Ioc (a 0) (a N) union Ioc (a N) (a (N + 1)) := Ioc_subset_Ioc_union_Ioc
    _ subseteq _ := by simpa [Finset.range_add_one] using
                  union_subset_union_right (Ioc (a N) (a (N + 1))) ih

Depends on / 依赖: Finset, Finset.range_add_one, Ioc_subset_Ioc_union_Ioc, range_add_one, subseteq, union_subset_union_right
-/
theorem Ioc_subset_biUnion_Ioc {X : Type*} [LinearOrder X] (N : Nat) (a : Nat -> X) :
    Ioc (a 0) (a N) subseteq ⋃ i in Finset.range N, Ioc (a i) (a (i + 1)) := by
  induction N with
  | zero => simp
  | succ N ih => calc
    _ subseteq Ioc (a 0) (a N) union Ioc (a N) (a (N + 1)) := Ioc_subset_Ioc_union_Ioc
    _ subseteq _ := by simpa [Finset.range_add_one] using
                  union_subset_union_right (Ioc (a N) (a (N + 1))) ih

/--
theorem `Ico_subset_biUnion_Ico` / 定理 `Ico_subset_biUnion_Ico`

English:
theorem Ico_subset_biUnion_Ico
  given: {X : Type*} [LinearOrder X] (N : Nat) (a : Nat -> X)
  proof: by
  induction N with
  | zero => simp
  | succ N ih => calc
    _ subseteq Ico (a 0) (a N) union Ico (a N) (a (N + 1)) := Ico_subset_Ico_union_Ico
    _ subseteq _ := by simpa [Finset.range_add_one] using
                  union_subset_union_right (Ico (a N) (a (N + 1))) ih

中文:
定理 Ico_subset_biUnion_Ico
  条件: {X : 类型} [线性序 X] (N : 自然数) (a : 自然数 -> X)
  证明: by
  induction N with
  | zero => simp
  | succ N ih => calc
    _ subseteq Ico (a 0) (a N) union Ico (a N) (a (N + 1)) := Ico_subset_Ico_union_Ico
    _ subseteq _ := by simpa [Finset.range_add_one] using
                  union_subset_union_right (Ico (a N) (a (N + 1))) ih

Depends on / 依赖: Finset, Finset.range_add_one, Ico_subset_Ico_union_Ico, range_add_one, subseteq, union_subset_union_right
-/
theorem Ico_subset_biUnion_Ico {X : Type*} [LinearOrder X] (N : Nat) (a : Nat -> X) :
    Ico (a 0) (a N) subseteq ⋃ i in Finset.range N, Ico (a i) (a (i + 1)) := by
  induction N with
  | zero => simp
  | succ N ih => calc
    _ subseteq Ico (a 0) (a N) union Ico (a N) (a (N + 1)) := Ico_subset_Ico_union_Ico
    _ subseteq _ := by simpa [Finset.range_add_one] using
                  union_subset_union_right (Ico (a N) (a (N + 1))) ih
