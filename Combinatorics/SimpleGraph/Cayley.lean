/-
Copyright (c) 2026 Edward van de Meent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward van de Meent
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
### Definition of Cayley graphs

This file defines and proves several fact about Cayley graphs.
A Cayley graph over type `M` with generators `s : Set M` is a graph in which two vertices `u ≠ v`
are adjacent if and only if there is some `g ∈ s` such that `u * g = v` or `v * g = u`.
The elements of `s` are called generators.

## Main declarations

* `SimpleGraph.mulCayley s`: the Cayley graph over `M` induced by `[Mul M]` with generators `s`.
* `SimpleGraph.addCayley s`: the Cayley graph over `M` induced by `[Add M]` with generators `s`.

## TODOS
* Add API describing behaviour w/r/t `MulOpposite`.
* Add lemma showing this graph is the same as `SimpleGraph.circulantGraph` in appropriate settings.

-/

@[expose] public section

namespace SimpleGraph

/-- The Cayley graph induced by an operation `[Mul M]` with generators `s` -/
@[to_additive /-- The Cayley graph induced by an operation `[Add M]` with generators `s` -/]
/--
Definition of `mulCayley` / `mulCayley` 的定义

English:
definition mulCayley
  signature: {M : Type*} (s : Set M) [Mul M]
  body: fromRel (exists g in s, · * g = ·)

中文:
定义 mulCayley
  签名: {M : 类型} (s : Set M) [Mul M]
  定义体: fromRel (exists g in s, · * g = ·)

Depends on / 依赖: fromRel
-/
def mulCayley {M : Type*} (s : Set M) [Mul M] : SimpleGraph M :=
  fromRel (exists g in s, · * g = ·)

variable {M : Type*} (s : Set M)

section Mul
variable [Mul M]

/-- See `mulCayley_adj` for the more convenient form in a `Group`. -/
@[to_additive /-- See `addCayley_adj` for the more convenient form in an `AddGroup`. -/]
/--
lemma `mulCayley_adj'` / 引理 `mulCayley_adj'`

English:
lemma mulCayley_adj'
  given: (u v : M)
  proof: by
  simp [mulCayley, ← exists_or, ← and_or_left, eq_comm]

@[to_additive]

中文:
引理 mulCayley_adj'
  条件: (u v : M)
  证明: by
  simp [mulCayley, ← exists_or, ← and_or_left, eq_comm]

@[to_additive]

Depends on / 依赖: and_or_left, eq_comm, exists_or, mulCayley
-/
lemma mulCayley_adj' (u v : M) :
    (mulCayley s).Adj u v ↔ u != v ∧ exists g in s, u * g = v ∨ u = v * g := by
  simp [mulCayley, ← exists_or, ← and_or_left, eq_comm]

@[to_additive]
/--
lemma `mulCayley_le_iff` / 引理 `mulCayley_le_iff`

English:
lemma mulCayley_le_iff
  given: (G : SimpleGraph M)
  proof: by
  rw [SimpleGraph.le_iff_adj]
  simp only [mulCayley_adj', ne_eq, and_imp, forall_exists_index]
  constructor
  · intro h g hg a ha
    exact h (a * g) a ha g hg (Or.inr rfl)
  · rintro h v w hvw g hg (rfl | rfl)
    · exact (h g hg v (hvw ·.symm)).symm
    · exact h g hg w hvw

@[to_additive]

中文:
引理 mulCayley_le_iff
  条件: (G : SimpleGraph M)
  证明: by
  rw [SimpleGraph.le_iff_adj]
  simp only [mulCayley_adj', ne_eq, and_imp, forall_exists_index]
  constructor
  · intro h g hg a ha
    exact h (a * g) a ha g hg (Or.inr rfl)
  · rintro h v w hvw g hg (rfl | rfl)
    · exact (h g hg v (hvw ·.symm)).symm
    · exact h g hg w hvw

@[to_additive]

Depends on / 依赖: Or.inr, SimpleGraph, SimpleGraph.le_iff_adj, and_imp, forall_exists_index, le_iff_adj, mulCayley_adj, ne_eq
-/
lemma mulCayley_le_iff (G : SimpleGraph M) :
    mulCayley s <= G ↔ forall g in s, forall a, a * g != a -> G.Adj (a * g) a := by
  rw [SimpleGraph.le_iff_adj]
  simp only [mulCayley_adj', ne_eq, and_imp, forall_exists_index]
  constructor
  · intro h g hg a ha
    exact h (a * g) a ha g hg (Or.inr rfl)
  · rintro h v w hvw g hg (rfl | rfl)
    · exact (h g hg v (hvw ·.symm)).symm
    · exact h g hg w hvw

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fintype
  signature: M] [DecidableEq M] [DecidablePred (· in s)] :
  body: fun u v =>
  decidable_of_iff (u != v ∧ exists g in s, u * g = v ∨ u = v * g) (mulCayley_adj' s u v).symm

中文:
实例 [Fintype
  签名: M] [DecidableEq M] [DecidablePred (· in s)] :
  定义体: fun u v =>
  decidable_of_iff (u != v ∧ exists g in s, u * g = v ∨ u = v * g) (mulCayley_adj' s u v).symm
-/
instance [Fintype M] [DecidableEq M] [DecidablePred (· in s)] :
    DecidableRel (mulCayley s).Adj := fun u v =>
  decidable_of_iff (u != v ∧ exists g in s, u * g = v ∨ u = v * g) (mulCayley_adj' s u v).symm

variable (M) in
/-- `mulCayley` is a left (order-)adjoint. -/
@[to_additive /-- `addCayley` is a left (order-)adjoint. -/]
/--
lemma `mulCayley_gc` / 引理 `mulCayley_gc`

English:
lemma mulCayley_gc
  proof: by
  intro S G
  simp [mulCayley_le_iff, Set.subset_def]

@[to_additive]

中文:
引理 mulCayley_gc
  证明: by
  intro S G
  simp [mulCayley_le_iff, Set.subset_def]

@[to_additive]

Depends on / 依赖: Set.subset_def, mulCayley_le_iff, subset_def
-/
lemma mulCayley_gc :
    GaloisConnection (mulCayley ·) ({g : M | forall a, a * g != a -> ·.Adj (a * g) a}) := by
  intro S G
  simp [mulCayley_le_iff, Set.subset_def]

@[to_additive]
/--
theorem `mulCayley_monotone` / 定理 `mulCayley_monotone`

English:
theorem mulCayley_monotone
  statement: Monotone (mulCayley (M := M) ·)
  proof: (mulCayley_gc M).monotone_l

@[to_additive (attr := gcongr)]

中文:
定理 mulCayley_monotone
  结论: Monotone (mulCayley (M := M) ·)
  证明: (mulCayley_gc M).monotone_l

@[to_additive (attr := gcongr)]
-/
theorem mulCayley_monotone : Monotone (mulCayley (M := M) ·) :=
  (mulCayley_gc M).monotone_l

@[to_additive (attr := gcongr)]
/--
theorem `mulCayley_mono` / 定理 `mulCayley_mono`

English:
theorem mulCayley_mono
  given: {U V : Set M} (hUV : U subseteq V)
  statement: mulCayley U <= mulCayley V
  proof: mulCayley_monotone hUV

@[to_additive (attr := simp)]

中文:
定理 mulCayley_mono
  条件: {U V : Set M} (hUV : U subseteq V)
  结论: mulCayley U <= mulCayley V
  证明: mulCayley_monotone hUV

@[to_additive (attr := simp)]

Depends on / 依赖: mulCayley_monotone
-/
theorem mulCayley_mono {U V : Set M} (hUV : U subseteq V) : mulCayley U <= mulCayley V :=
  mulCayley_monotone hUV

@[to_additive (attr := simp)]
/--
theorem `mulCayley_empty` / 定理 `mulCayley_empty`

English:
theorem mulCayley_empty
  statement: mulCayley (∅ : Set M) = ⊥
  proof: (mulCayley_gc M).l_bot

@[to_additive (attr := simp)]

中文:
定理 mulCayley_empty
  结论: mulCayley (∅ : Set M) = ⊥
  证明: (mulCayley_gc M).l_bot

@[to_additive (attr := simp)]

Depends on / 依赖: l_bot, mulCayley_gc
-/
theorem mulCayley_empty : mulCayley (∅ : Set M) = ⊥ := (mulCayley_gc M).l_bot

@[to_additive (attr := simp)]
/--
theorem `mulCayley_union` / 定理 `mulCayley_union`

English:
theorem mulCayley_union
  given: (s₁ s₂ : Set M)
  statement: mulCayley (s₁ union s₂) = mulCayley s₁ ⊔ mulCayley s₂
  proof: (mulCayley_gc M).l_sup

中文:
定理 mulCayley_union
  条件: (s₁ s₂ : Set M)
  结论: mulCayley (s₁ union s₂) = mulCayley s₁ ⊔ mulCayley s₂
  证明: (mulCayley_gc M).l_sup

Depends on / 依赖: l_sup, mulCayley_gc
-/
theorem mulCayley_union (s₁ s₂ : Set M) : mulCayley (s₁ union s₂) = mulCayley s₁ ⊔ mulCayley s₂ :=
  (mulCayley_gc M).l_sup

end Mul

section Semigroup
variable [Semigroup M]

@[to_additive (attr := simp)]
/--
theorem `mulCayley_adj_mul_iff_right` / 定理 `mulCayley_adj_mul_iff_right`

English:
theorem mulCayley_adj_mul_iff_right
  given: [IsLeftCancelMul M] {s : Set M} {u v d : M}
  proof: by
  simp [mulCayley_adj', mul_assoc]

中文:
定理 mulCayley_adj_mul_iff_right
  条件: [IsLeftCancelMul M] {s : Set M} {u v d : M}
  证明: by
  simp [mulCayley_adj', mul_assoc]

Depends on / 依赖: mulCayley_adj, mul_assoc
-/
theorem mulCayley_adj_mul_iff_right [IsLeftCancelMul M] {s : Set M} {u v d : M} :
    (mulCayley s).Adj (d * u) (d * v) ↔ (mulCayley s).Adj u v := by
  simp [mulCayley_adj', mul_assoc]

end Semigroup

section MulOneClass
variable [MulOneClass M]

@[to_additive (attr := simp)]
/--
theorem `mulCayley_erase_one` / 定理 `mulCayley_erase_one`

English:
theorem mulCayley_erase_one
  statement: mulCayley (s \ {1}) = mulCayley s
  proof: by
  nth_rw 2 [← Set.sdiff_union_inter s {1}]
  rw [mulCayley_union]
  ext u v
  simp +contextual [mulCayley_adj']

@[to_additive (attr := simp)]

中文:
定理 mulCayley_erase_one
  结论: mulCayley (s \ {1}) = mulCayley s
  证明: by
  nth_rw 2 [← Set.sdiff_union_inter s {1}]
  rw [mulCayley_union]
  ext u v
  simp +contextual [mulCayley_adj']

@[to_additive (attr := simp)]

Depends on / 依赖: Set.sdiff_union_inter, contextual, mulCayley_adj, mulCayley_union, nth_rw, sdiff_union_inter
-/
theorem mulCayley_erase_one : mulCayley (s \ {1}) = mulCayley s := by
  nth_rw 2 [← Set.sdiff_union_inter s {1}]
  rw [mulCayley_union]
  ext u v
  simp +contextual [mulCayley_adj']

@[to_additive (attr := simp)]
/--
theorem `mulCayley_insert_one` / 定理 `mulCayley_insert_one`

English:
theorem mulCayley_insert_one
  statement: mulCayley (insert 1 s) = mulCayley s
  proof: by
  simp [← Set.union_singleton, ← mulCayley_erase_one]

@[to_additive (attr := simp)]

中文:
定理 mulCayley_insert_one
  结论: mulCayley (insert 1 s) = mulCayley s
  证明: by
  simp [← Set.union_singleton, ← mulCayley_erase_one]

@[to_additive (attr := simp)]

Depends on / 依赖: Set.union_singleton, mulCayley_erase_one, union_singleton
-/
theorem mulCayley_insert_one : mulCayley (insert 1 s) = mulCayley s := by
  simp [← Set.union_singleton, ← mulCayley_erase_one]

@[to_additive (attr := simp)]
/--
theorem `mulCayley_singleton_one` / 定理 `mulCayley_singleton_one`

English:
theorem mulCayley_singleton_one
  statement: mulCayley ({1} : Set M) = ⊥
  proof: by
  rw [← mulCayley_erase_one]; rw [Set.sdiff_self]; rw [mulCayley_empty]

中文:
定理 mulCayley_singleton_one
  结论: mulCayley ({1} : Set M) = ⊥
  证明: by
  rw [← mulCayley_erase_one]; rw [Set.sdiff_self]; rw [mulCayley_empty]

Depends on / 依赖: Set.sdiff_self, mulCayley_empty, mulCayley_erase_one, sdiff_self
-/
theorem mulCayley_singleton_one : mulCayley ({1} : Set M) = ⊥ := by
  rw [← mulCayley_erase_one]; rw [Set.sdiff_self]; rw [mulCayley_empty]

end MulOneClass
section Group
variable [Group M]

@[to_additive]
/--
lemma `mulCayley_adj` / 引理 `mulCayley_adj`

English:
lemma mulCayley_adj
  given: (u v : M)
  proof: by
  simp [mulCayley_adj', ← eq_inv_mul_iff_mul_eq (b := u), ← inv_mul_eq_iff_eq_mul (a := v),
    and_or_left, exists_or]

@[to_additive (attr := simp)]

中文:
引理 mulCayley_adj
  条件: (u v : M)
  证明: by
  simp [mulCayley_adj', ← eq_inv_mul_iff_mul_eq (b := u), ← inv_mul_eq_iff_eq_mul (a := v),
    and_or_left, exists_or]

@[to_additive (attr := simp)]

Depends on / 依赖: and_or_left, eq_inv_mul_iff_mul_eq, exists_or, inv_mul_eq_iff_eq_mul, mulCayley_adj
-/
lemma mulCayley_adj (u v : M) :
    (mulCayley s).Adj u v ↔ u != v ∧ (u⁻¹ * v in s ∨ v⁻¹ * u in s) := by
  simp [mulCayley_adj', ← eq_inv_mul_iff_mul_eq (b := u), ← inv_mul_eq_iff_eq_mul (a := v),
    and_or_left, exists_or]

@[to_additive (attr := simp)]
/--
theorem `mulCayley_inv` / 定理 `mulCayley_inv`

English:
theorem mulCayley_inv
  statement: mulCayley s⁻¹ = mulCayley s
  proof: by
  ext u v
  simp [mulCayley_adj, or_comm]

@[to_additive]

中文:
定理 mulCayley_inv
  结论: mulCayley s⁻¹ = mulCayley s
  证明: by
  ext u v
  simp [mulCayley_adj, or_comm]

@[to_additive]

Depends on / 依赖: mulCayley_adj, or_comm
-/
theorem mulCayley_inv : mulCayley s⁻¹ = mulCayley s := by
  ext u v
  simp [mulCayley_adj, or_comm]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: M] [DecidablePred (· in s)] : DecidableRel (mulCayley s).Adj
  body: fun u v => decidable_of_iff (u != v ∧ (u⁻¹ * v in s ∨ v⁻¹ * u in s)) (mulCayley_adj s u v).symm

@[to_additive (attr := simp)]

中文:
实例 [DecidableEq
  签名: M] [DecidablePred (· in s)] : DecidableRel (mulCayley s).Adj
  定义体: fun u v => decidable_of_iff (u != v ∧ (u⁻¹ * v in s ∨ v⁻¹ * u in s)) (mulCayley_adj s u v).symm

@[to_additive (attr := simp)]

Depends on / 依赖: decidable_of_iff, mulCayley_adj
-/
instance [DecidableEq M] [DecidablePred (· in s)] : DecidableRel (mulCayley s).Adj :=
  fun u v => decidable_of_iff (u != v ∧ (u⁻¹ * v in s ∨ v⁻¹ * u in s)) (mulCayley_adj s u v).symm

@[to_additive (attr := simp)]
/--
theorem `mulCayley_univ` / 定理 `mulCayley_univ`

English:
theorem mulCayley_univ
  statement: mulCayley (Set.univ : Set M) = ⊤
  proof: by
  ext _ _
  simp [mulCayley_adj]

@[to_additive (attr := simp)]

中文:
定理 mulCayley_univ
  结论: mulCayley (Set.univ : Set M) = ⊤
  证明: by
  ext _ _
  simp [mulCayley_adj]

@[to_additive (attr := simp)]

Depends on / 依赖: mulCayley_adj
-/
theorem mulCayley_univ : mulCayley (Set.univ : Set M) = ⊤ := by
  ext _ _
  simp [mulCayley_adj]

@[to_additive (attr := simp)]
/--
theorem `mulCayley_compl_singleton_one` / 定理 `mulCayley_compl_singleton_one`

English:
theorem mulCayley_compl_singleton_one
  statement: mulCayley ({1}ᶜ : Set M) = ⊤
  proof: by
  simp [Set.compl_eq_univ_sdiff]

中文:
定理 mulCayley_compl_singleton_one
  结论: mulCayley ({1}ᶜ : Set M) = ⊤
  证明: by
  simp [Set.compl_eq_univ_sdiff]

Depends on / 依赖: Set.compl_eq_univ_sdiff, compl_eq_univ_sdiff
-/
theorem mulCayley_compl_singleton_one : mulCayley ({1}ᶜ : Set M) = ⊤ := by
  simp [Set.compl_eq_univ_sdiff]

end Group

end SimpleGraph
