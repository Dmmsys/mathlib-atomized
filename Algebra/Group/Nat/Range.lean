/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Embedding
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Finset.Image

/-!
# `Finset.range` and addition of natural numbers
-/

public section
assert_not_exists MonoidWithZero MulAction IsOrderedMonoid

variable {α β γ : Type*}

namespace Finset

/--
theorem `disjoint_range_addLeftEmbedding` / 定理 `disjoint_range_addLeftEmbedding`

English:
theorem disjoint_range_addLeftEmbedding
  given: (a : Nat) (s : Finset Nat)
  proof: by
  simp_rw [disjoint_left, mem_map, mem_range, addLeftEmbedding_apply]
  rintro _ h ⟨l, -, rfl⟩
  lia

中文:
定理 disjoint_range_addLeftEmbedding
  条件: (a : 自然数) (s : Finset 自然数)
  证明: by
  simp_rw [disjoint_left, mem_map, mem_range, addLeftEmbedding_apply]
  rintro _ h ⟨l, -, rfl⟩
  lia

Depends on / 依赖: addLeftEmbedding_apply, disjoint_left, mem_map, mem_range, simp_rw
-/
theorem disjoint_range_addLeftEmbedding (a : Nat) (s : Finset Nat) :
    Disjoint (range a) (map (addLeftEmbedding a) s) := by
  simp_rw [disjoint_left, mem_map, mem_range, addLeftEmbedding_apply]
  rintro _ h ⟨l, -, rfl⟩
  lia

/--
theorem `disjoint_range_addRightEmbedding` / 定理 `disjoint_range_addRightEmbedding`

English:
theorem disjoint_range_addRightEmbedding
  given: (a : Nat) (s : Finset Nat)
  proof: by
  rw [← addLeftEmbedding_eq_addRightEmbedding]
  apply disjoint_range_addLeftEmbedding

中文:
定理 disjoint_range_addRightEmbedding
  条件: (a : 自然数) (s : Finset 自然数)
  证明: by
  rw [← addLeftEmbedding_eq_addRightEmbedding]
  apply disjoint_range_addLeftEmbedding

Depends on / 依赖: addLeftEmbedding_eq_addRightEmbedding, disjoint_range_addLeftEmbedding
-/
theorem disjoint_range_addRightEmbedding (a : Nat) (s : Finset Nat) :
    Disjoint (range a) (map (addRightEmbedding a) s) := by
  rw [← addLeftEmbedding_eq_addRightEmbedding]
  apply disjoint_range_addLeftEmbedding

/--
theorem `range_add` / 定理 `range_add`

English:
theorem range_add
  given: (a b : Nat)
  statement: range (a + b) = range a union (range b).map (addLeftEmbedding a)
  proof: by
  rw [← val_inj]; rw [union_val]
  exact Multiset.range_add_eq_union a b

中文:
定理 range_add
  条件: (a b : 自然数)
  结论: range (a + b) = range a union (range b).map (addLeftEmbedding a)
  证明: by
  rw [← val_inj]; rw [union_val]
  exact Multiset.range_add_eq_union a b

Depends on / 依赖: Multiset, Multiset.range_add_eq_union, range_add_eq_union, union_val, val_inj
-/
theorem range_add (a b : Nat) : range (a + b) = range a union (range b).map (addLeftEmbedding a) := by
  rw [← val_inj]; rw [union_val]
  exact Multiset.range_add_eq_union a b

end Finset
