/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kyle Miller
-/
module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Finite.Vector

/-!
# Finiteness of sets of lists

## Tags

finite sets
-/

public section

assert_not_exists IsOrderedRing MonoidWithZero

namespace List
variable (α : Type*) [Finite α] (n : Nat)

/--
lemma `finite_length_eq` / 引理 `finite_length_eq`

English:
lemma finite_length_eq
  statement: {l : List α | l.length = n}.Finite
  proof: List.Vector.finite

中文:
引理 finite_length_eq
  结论: {l : List α | l.length = n}.Finite
  证明: List.Vector.finite

Depends on / 依赖: List.Vector.finite, Vector, finite
-/
lemma finite_length_eq : {l : List α | l.length = n}.Finite := List.Vector.finite

/--
lemma `finite_length_lt` / 引理 `finite_length_lt`

English:
lemma finite_length_lt
  statement: {l : List α | l.length < n}.Finite
  proof: by
  convert! (Finset.range n).finite_toSet.biUnion fun i _ => finite_length_eq α i; ext; simp

中文:
引理 finite_length_lt
  结论: {l : List α | l.length < n}.Finite
  证明: by
  convert! (Finset.range n).finite_toSet.biUnion fun i _ => finite_length_eq α i; ext; simp

Depends on / 依赖: Finset, Finset.range, biUnion, convert, finite_length_eq, finite_toSet, finite_toSet.biUnion
-/
lemma finite_length_lt : {l : List α | l.length < n}.Finite := by
  convert! (Finset.range n).finite_toSet.biUnion fun i _ => finite_length_eq α i; ext; simp

/--
lemma `finite_length_le` / 引理 `finite_length_le`

English:
lemma finite_length_le
  statement: {l : List α | l.length <= n}.Finite
  proof: by
  simpa [Nat.lt_succ_iff] using finite_length_lt α (n + 1)

中文:
引理 finite_length_le
  结论: {l : List α | l.length <= n}.Finite
  证明: by
  simpa [Nat.lt_succ_iff] using finite_length_lt α (n + 1)

Depends on / 依赖: Nat.lt_succ_iff, finite_length_lt, lt_succ_iff
-/
lemma finite_length_le : {l : List α | l.length <= n}.Finite := by
  simpa [Nat.lt_succ_iff] using finite_length_lt α (n + 1)

end List
