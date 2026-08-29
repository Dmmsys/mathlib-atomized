/-
Copyright (c) 2024 Lagrange Mathematics and Computing Research Center. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Bordg
-/
module

public import Mathlib.Data.Rel

/-!
# The Galois Connection Induced by a Relation

In this file, we show that an arbitrary relation `R` between a pair of types `α` and `β` defines
a pair `toDual ∘ R.leftDual` and `R.rightDual ∘ ofDual` of adjoint order-preserving maps between the
corresponding posets `Set α` and `(Set β)ᵒᵈ`.
We define `R.leftFixedPoints` (resp. `R.rightFixedPoints`) as the set of fixed points `J`
(resp. `I`) of `Set α` (resp. `Set β`) such that `rightDual (leftDual J) = J`
(resp. `leftDual (rightDual I) = I`).

## Main Results

⋆ `Rel.gc_leftDual_rightDual`: we prove that the maps `toDual ∘ R.leftDual` and
  `R.rightDual ∘ ofDual` form a Galois connection.
⋆ `Rel.equivFixedPoints`: we prove that the maps `R.leftDual` and `R.rightDual` induce inverse
  bijections between the sets of fixed points.

## References

⋆ Engendrement de topologies, démontrabilité et opérations sur les sous-topos, Olivia Caramello and
  Laurent Lafforgue (in preparation)

## Tags

relation, Galois connection, induced bijection, fixed points
-/

@[expose] public section

variable {α β : Type*} (R : SetRel α β)

namespace SetRel

/-! ### Pairs of adjoint maps defined by relations -/

open OrderDual

/--
Definition of `leftDual` / `leftDual` 的定义

English:
definition leftDual
  signature: (J : Set α)
  body: {b : β | forall ⦃a⦄, a in J -> a ~[R] b}

中文:
定义 leftDual
  签名: (J : 集合 α)
  定义体: {b : β | forall ⦃a⦄, a in J -> a ~[R] b}
-/
def leftDual (J : Set α) : Set β := {b : β | forall ⦃a⦄, a in J -> a ~[R] b}

/--
Definition of `rightDual` / `rightDual` 的定义

English:
definition rightDual
  signature: (I : Set β)
  body: {a : α | forall ⦃b⦄, b in I -> a ~[R] b}

中文:
定义 rightDual
  签名: (I : 集合 β)
  定义体: {a : α | forall ⦃b⦄, b in I -> a ~[R] b}
-/
def rightDual (I : Set β) : Set α := {a : α | forall ⦃b⦄, b in I -> a ~[R] b}

/--
theorem `gc_leftDual_rightDual` / 定理 `gc_leftDual_rightDual`

English:
theorem gc_leftDual_rightDual
  statement: GaloisConnection (toDual ∘ R.leftDual) (R.rightDual ∘ ofDual)
  proof: fun _ _ => ⟨fun h _ ha _ hb => h (by simpa) ha, fun h _ hb _ ha => h (by simpa) hb⟩

中文:
定理 gc_leftDual_rightDual
  结论: GaloisConnection (toDual ∘ R.leftDual) (R.rightDual ∘ ofDual)
  证明: fun _ _ => ⟨fun h _ ha _ hb => h (by simpa) ha, fun h _ hb _ ha => h (by simpa) hb⟩
-/
theorem gc_leftDual_rightDual : GaloisConnection (toDual ∘ R.leftDual) (R.rightDual ∘ ofDual) :=
  fun _ _ => ⟨fun h _ ha _ hb => h (by simpa) ha, fun h _ hb _ ha => h (by simpa) hb⟩

/-! ### Induced equivalences between fixed points -/

/--
Definition of `leftFixedPoints` / `leftFixedPoints` 的定义

English:
definition leftFixedPoints
  body: {J : Set α | R.rightDual (R.leftDual J) = J}

中文:
定义 leftFixedPoints
  定义体: {J : Set α | R.rightDual (R.leftDual J) = J}

Depends on / 依赖: R.leftDual, R.rightDual, leftDual, rightDual
-/
def leftFixedPoints := {J : Set α | R.rightDual (R.leftDual J) = J}

/--
Definition of `rightFixedPoints` / `rightFixedPoints` 的定义

English:
definition rightFixedPoints
  body: {I : Set β | R.leftDual (R.rightDual I) = I}

中文:
定义 rightFixedPoints
  定义体: {I : Set β | R.leftDual (R.rightDual I) = I}

Depends on / 依赖: R.leftDual, R.rightDual, leftDual, rightDual
-/
def rightFixedPoints := {I : Set β | R.leftDual (R.rightDual I) = I}

open GaloisConnection

/--
theorem `leftDual_mem_rightFixedPoint` / 定理 `leftDual_mem_rightFixedPoint`

English:
theorem leftDual_mem_rightFixedPoint
  given: (J : Set α)
  statement: R.leftDual J in R.rightFixedPoints
  proof: by
  apply le_antisymm
  · apply R.gc_leftDual_rightDual.monotone_l; exact R.gc_leftDual_rightDual.le_u_l J
  · exact R.gc_leftDual_rightDual.l_u_le (R.leftDual J)

中文:
定理 leftDual_mem_rightFixedPoint
  条件: (J : 集合 α)
  结论: R.leftDual J in R.rightFixedPoints
  证明: by
  apply le_antisymm
  · apply R.gc_leftDual_rightDual.monotone_l; exact R.gc_leftDual_rightDual.le_u_l J
  · exact R.gc_leftDual_rightDual.l_u_le (R.leftDual J)

Depends on / 依赖: R.gc_leftDual_rightDual.l_u_le, R.gc_leftDual_rightDual.le_u_l, R.gc_leftDual_rightDual.monotone_l, R.leftDual, gc_leftDual_rightDual, l_u_le, le_antisymm, le_u_l, leftDual, monotone_l
-/
theorem leftDual_mem_rightFixedPoint (J : Set α) : R.leftDual J in R.rightFixedPoints := by
  apply le_antisymm
  · apply R.gc_leftDual_rightDual.monotone_l; exact R.gc_leftDual_rightDual.le_u_l J
  · exact R.gc_leftDual_rightDual.l_u_le (R.leftDual J)

/--
theorem `rightDual_mem_leftFixedPoint` / 定理 `rightDual_mem_leftFixedPoint`

English:
theorem rightDual_mem_leftFixedPoint
  given: (I : Set β)
  statement: R.rightDual I in R.leftFixedPoints
  proof: by
  apply le_antisymm
  · apply R.gc_leftDual_rightDual.monotone_u; exact R.gc_leftDual_rightDual.l_u_le I
  · exact R.gc_leftDual_rightDual.le_u_l (R.rightDual I)

中文:
定理 rightDual_mem_leftFixedPoint
  条件: (I : 集合 β)
  结论: R.rightDual I in R.leftFixedPoints
  证明: by
  apply le_antisymm
  · apply R.gc_leftDual_rightDual.monotone_u; exact R.gc_leftDual_rightDual.l_u_le I
  · exact R.gc_leftDual_rightDual.le_u_l (R.rightDual I)

Depends on / 依赖: R.gc_leftDual_rightDual.l_u_le, R.gc_leftDual_rightDual.le_u_l, R.gc_leftDual_rightDual.monotone_u, R.rightDual, gc_leftDual_rightDual, l_u_le, le_antisymm, le_u_l, monotone_u, rightDual
-/
theorem rightDual_mem_leftFixedPoint (I : Set β) : R.rightDual I in R.leftFixedPoints := by
  apply le_antisymm
  · apply R.gc_leftDual_rightDual.monotone_u; exact R.gc_leftDual_rightDual.l_u_le I
  · exact R.gc_leftDual_rightDual.le_u_l (R.rightDual I)

/--
Definition of `equivFixedPoints` / `equivFixedPoints` 的定义

English:
definition equivFixedPoints
  signature: : R.leftFixedPoints ≃ R.rightFixedPoints where
  body: fun ⟨J, _⟩ => ⟨R.leftDual J, R.leftDual_mem_rightFixedPoint J⟩
  invFun := fun ⟨I, _⟩ => ⟨R.rightDual I, R.rightDual_mem_leftFixedPoint I⟩
  left_inv J := by obtain ⟨J, hJ⟩ := J; rw [Subtype.mk.injEq, hJ]
  right_inv I := by obtain ⟨I, hI⟩ := I; rw [Subtype.mk.injEq, hI]

中文:
定义 equivFixedPoints
  签名: : R.leftFixedPoints ≃ R.rightFixedPoints where
  定义体: fun ⟨J, _⟩ => ⟨R.leftDual J, R.leftDual_mem_rightFixedPoint J⟩
  invFun := fun ⟨I, _⟩ => ⟨R.rightDual I, R.rightDual_mem_leftFixedPoint I⟩
  left_inv J := by obtain ⟨J, hJ⟩ := J; rw [Subtype.mk.injEq, hJ]
  right_inv I := by obtain ⟨I, hI⟩ := I; rw [Subtype.mk.injEq, hI]

Depends on / 依赖: R.leftDual, R.leftDual_mem_rightFixedPoint, leftDual, leftDual_mem_rightFixedPoint
-/
def equivFixedPoints : R.leftFixedPoints ≃ R.rightFixedPoints where
  toFun := fun ⟨J, _⟩ => ⟨R.leftDual J, R.leftDual_mem_rightFixedPoint J⟩
  invFun := fun ⟨I, _⟩ => ⟨R.rightDual I, R.rightDual_mem_leftFixedPoint I⟩
  left_inv J := by obtain ⟨J, hJ⟩ := J; rw [Subtype.mk.injEq, hJ]
  right_inv I := by obtain ⟨I, hI⟩ := I; rw [Subtype.mk.injEq, hI]

/--
theorem `rightDual_leftDual_le_of_le` / 定理 `rightDual_leftDual_le_of_le`

English:
theorem rightDual_leftDual_le_of_le
  given: {J J' : Set α} (h : J' in R.leftFixedPoints) (h₁ : J <= J')
  proof: by
  rw [← h]
  apply R.gc_leftDual_rightDual.monotone_u
  apply R.gc_leftDual_rightDual.monotone_l
  exact h₁

中文:
定理 rightDual_leftDual_le_of_le
  条件: {J J' : 集合 α} (h : J' in R.leftFixedPoints) (h₁ : J <= J')
  证明: by
  rw [← h]
  apply R.gc_leftDual_rightDual.monotone_u
  apply R.gc_leftDual_rightDual.monotone_l
  exact h₁

Depends on / 依赖: R.gc_leftDual_rightDual.monotone_l, R.gc_leftDual_rightDual.monotone_u, gc_leftDual_rightDual, monotone_l, monotone_u
-/
theorem rightDual_leftDual_le_of_le {J J' : Set α} (h : J' in R.leftFixedPoints) (h₁ : J <= J') :
    R.rightDual (R.leftDual J) <= J' := by
  rw [← h]
  apply R.gc_leftDual_rightDual.monotone_u
  apply R.gc_leftDual_rightDual.monotone_l
  exact h₁

/--
theorem `leftDual_rightDual_le_of_le` / 定理 `leftDual_rightDual_le_of_le`

English:
theorem leftDual_rightDual_le_of_le
  given: {I I' : Set β} (h : I' in R.rightFixedPoints) (h₁ : I <= I')
  proof: by
  rw [← h]
  apply R.gc_leftDual_rightDual.monotone_l
  apply R.gc_leftDual_rightDual.monotone_u
  exact h₁

中文:
定理 leftDual_rightDual_le_of_le
  条件: {I I' : 集合 β} (h : I' in R.rightFixedPoints) (h₁ : I <= I')
  证明: by
  rw [← h]
  apply R.gc_leftDual_rightDual.monotone_l
  apply R.gc_leftDual_rightDual.monotone_u
  exact h₁

Depends on / 依赖: R.gc_leftDual_rightDual.monotone_l, R.gc_leftDual_rightDual.monotone_u, gc_leftDual_rightDual, monotone_l, monotone_u
-/
theorem leftDual_rightDual_le_of_le {I I' : Set β} (h : I' in R.rightFixedPoints) (h₁ : I <= I') :
    R.leftDual (R.rightDual I) <= I' := by
  rw [← h]
  apply R.gc_leftDual_rightDual.monotone_l
  apply R.gc_leftDual_rightDual.monotone_u
  exact h₁

end SetRel
