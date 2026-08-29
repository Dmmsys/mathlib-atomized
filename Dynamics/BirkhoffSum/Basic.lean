/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Birkhoff sums

In this file we define `birkhoffSum f g n x` to be the sum `∑ k ∈ Finset.range n, g (f^[k] x)`.
This sum (more precisely, the corresponding average `n⁻¹ • birkhoffSum f g n x`)
appears in various ergodic theorems
saying that these averages converge to the "space average" `⨍ x, g x ∂μ` in some sense.

See also `birkhoffAverage` defined in `Dynamics/BirkhoffSum/Average`.
-/

@[expose] public section

open Finset Function

section AddCommMonoid

variable {α M : Type*} [AddCommMonoid M]

/--
Definition of `birkhoffSum` / `birkhoffSum` 的定义

English:
definition birkhoffSum
  signature: (f : α -> α) (g : α -> M) (n : Nat) (x : α)
  body: ∑ k in range n, g (f^[k] x)

中文:
定义 birkhoffSum
  签名: (f : α -> α) (g : α -> M) (n : 自然数) (x : α)
  定义体: ∑ k in range n, g (f^[k] x)
-/
def birkhoffSum (f : α -> α) (g : α -> M) (n : Nat) (x : α) : M := ∑ k in range n, g (f^[k] x)

/--
theorem `birkhoffSum_zero` / 定理 `birkhoffSum_zero`

English:
theorem birkhoffSum_zero
  given: (f : α -> α) (g : α -> M) (x : α)
  statement: birkhoffSum f g 0 x = 0
  proof: sum_range_zero _

@[simp]

中文:
定理 birkhoffSum_zero
  条件: (f : α -> α) (g : α -> M) (x : α)
  结论: birkhoffSum f g 0 x = 0
  证明: sum_range_zero _

@[simp]

Depends on / 依赖: sum_range_zero
-/
theorem birkhoffSum_zero (f : α -> α) (g : α -> M) (x : α) : birkhoffSum f g 0 x = 0 :=
  sum_range_zero _

@[simp]
/--
theorem `birkhoffSum_zero'` / 定理 `birkhoffSum_zero'`

English:
theorem birkhoffSum_zero'
  given: (f : α -> α) (g : α -> M)
  statement: birkhoffSum f g 0 = 0
  proof: funext birkhoffSum_zero _ _

中文:
定理 birkhoffSum_zero'
  条件: (f : α -> α) (g : α -> M)
  结论: birkhoffSum f g 0 = 0
  证明: funext birkhoffSum_zero _ _

Depends on / 依赖: birkhoffSum_zero
-/
theorem birkhoffSum_zero' (f : α -> α) (g : α -> M) : birkhoffSum f g 0 = 0 :=
funext birkhoffSum_zero _ _

/--
theorem `birkhoffSum_one` / 定理 `birkhoffSum_one`

English:
theorem birkhoffSum_one
  given: (f : α -> α) (g : α -> M) (x : α)
  statement: birkhoffSum f g 1 x = g x
  proof: sum_range_one _

@[simp]

中文:
定理 birkhoffSum_one
  条件: (f : α -> α) (g : α -> M) (x : α)
  结论: birkhoffSum f g 1 x = g x
  证明: sum_range_one _

@[simp]

Depends on / 依赖: sum_range_one
-/
theorem birkhoffSum_one (f : α -> α) (g : α -> M) (x : α) : birkhoffSum f g 1 x = g x :=
  sum_range_one _

@[simp]
/--
theorem `birkhoffSum_one'` / 定理 `birkhoffSum_one'`

English:
theorem birkhoffSum_one'
  given: (f : α -> α) (g : α -> M)
  statement: birkhoffSum f g 1 = g
  proof: funext birkhoffSum_one f g

中文:
定理 birkhoffSum_one'
  条件: (f : α -> α) (g : α -> M)
  结论: birkhoffSum f g 1 = g
  证明: funext birkhoffSum_one f g

Depends on / 依赖: birkhoffSum_one
-/
theorem birkhoffSum_one' (f : α -> α) (g : α -> M) : birkhoffSum f g 1 = g :=
funext birkhoffSum_one f g

/--
theorem `birkhoffSum_succ` / 定理 `birkhoffSum_succ`

English:
theorem birkhoffSum_succ
  given: (f : α -> α) (g : α -> M) (n : Nat) (x : α)
  proof: sum_range_succ _ _

中文:
定理 birkhoffSum_succ
  条件: (f : α -> α) (g : α -> M) (n : 自然数) (x : α)
  证明: sum_range_succ _ _

Depends on / 依赖: sum_range_succ
-/
theorem birkhoffSum_succ (f : α -> α) (g : α -> M) (n : Nat) (x : α) :
    birkhoffSum f g (n + 1) x = birkhoffSum f g n x + g (f^[n] x) :=
  sum_range_succ _ _

/--
theorem `birkhoffSum_succ'` / 定理 `birkhoffSum_succ'`

English:
theorem birkhoffSum_succ'
  given: (f : α -> α) (g : α -> M) (n : Nat) (x : α)
  proof: (sum_range_succ' _ _).trans (add_comm _ _)

中文:
定理 birkhoffSum_succ'
  条件: (f : α -> α) (g : α -> M) (n : 自然数) (x : α)
  证明: (sum_range_succ' _ _).trans (add_comm _ _)

Depends on / 依赖: add_comm, sum_range_succ
-/
theorem birkhoffSum_succ' (f : α -> α) (g : α -> M) (n : Nat) (x : α) :
    birkhoffSum f g (n + 1) x = g x + birkhoffSum f g n (f x) :=
  (sum_range_succ' _ _).trans (add_comm _ _)

/--
theorem `birkhoffSum_add` / 定理 `birkhoffSum_add`

English:
theorem birkhoffSum_add
  given: (f : α -> α) (g : α -> M) (m n : Nat) (x : α)
  proof: by
  simp_rw [birkhoffSum, sum_range_add, add_comm m, iterate_add_apply]

中文:
定理 birkhoffSum_add
  条件: (f : α -> α) (g : α -> M) (m n : 自然数) (x : α)
  证明: by
  simp_rw [birkhoffSum, sum_range_add, add_comm m, iterate_add_apply]

Depends on / 依赖: add_comm, birkhoffSum, iterate_add_apply, simp_rw, sum_range_add
-/
theorem birkhoffSum_add (f : α -> α) (g : α -> M) (m n : Nat) (x : α) :
    birkhoffSum f g (m + n) x = birkhoffSum f g m x + birkhoffSum f g n (f^[m] x) := by
  simp_rw [birkhoffSum, sum_range_add, add_comm m, iterate_add_apply]

/--
theorem `birkhoffSum_add'` / 定理 `birkhoffSum_add'`

English:
theorem birkhoffSum_add'
  given: (f : α -> α) (g g' : α -> M) (n : Nat) (x : α)
  proof: by
  simpa [birkhoffSum] using sum_add_distrib

中文:
定理 birkhoffSum_add'
  条件: (f : α -> α) (g g' : α -> M) (n : 自然数) (x : α)
  证明: by
  simpa [birkhoffSum] using sum_add_distrib

Depends on / 依赖: birkhoffSum, sum_add_distrib
-/
theorem birkhoffSum_add' (f : α -> α) (g g' : α -> M) (n : Nat) (x : α) :
    birkhoffSum f (g + g') n x = birkhoffSum f g n x + birkhoffSum f g' n x := by
  simpa [birkhoffSum] using sum_add_distrib

/--
theorem `Function.IsFixedPt.birkhoffSum_eq` / 定理 `Function.IsFixedPt.birkhoffSum_eq`

English:
theorem Function.IsFixedPt.birkhoffSum_eq
  statement: {f : α -> α} {x : α} (h : IsFixedPt f x) (g : α -> M)
  proof: by
  simp [birkhoffSum, (h.iterate _).eq]

中文:
定理 Function.IsFixedPt.birkhoffSum_eq
  结论: {f : α -> α} {x : α} (h : IsFixedPt f x) (g : α -> M)
  证明: by
  simp [birkhoffSum, (h.iterate _).eq]

Depends on / 依赖: birkhoffSum, h.iterate, iterate
-/
theorem Function.IsFixedPt.birkhoffSum_eq {f : α -> α} {x : α} (h : IsFixedPt f x) (g : α -> M)
    (n : Nat) : birkhoffSum f g n x = n • g x := by
  simp [birkhoffSum, (h.iterate _).eq]

/--
theorem `map_birkhoffSum` / 定理 `map_birkhoffSum`

English:
theorem map_birkhoffSum
  statement: {F N : Type*} [AddCommMonoid N] [FunLike F M N] [AddMonoidHomClass F M N]
  proof: map_sum g' _ _

中文:
定理 map_birkhoffSum
  结论: {F N : 类型} [AddCommMonoid N] [FunLike F M N] [AddMonoidHomClass F M N]
  证明: map_sum g' _ _

Depends on / 依赖: map_sum
-/
theorem map_birkhoffSum {F N : Type*} [AddCommMonoid N] [FunLike F M N] [AddMonoidHomClass F M N]
    (g' : F) (f : α -> α) (g : α -> M) (n : Nat) (x : α) :
    g' (birkhoffSum f g n x) = birkhoffSum f (g' ∘ g) n x :=
  map_sum g' _ _

/--
theorem `birkhoffSum_of_comp_eq` / 定理 `birkhoffSum_of_comp_eq`

English:
theorem birkhoffSum_of_comp_eq
  given: {f : α -> α} {φ : α -> M} (h : φ ∘ f = φ) (n : Nat)
  proof: by
  funext x
  suffices forall k, φ (f^[k] x) = φ x by simp [birkhoffSum, this]
  intro k
  exact congrFun (iterate_invariant h k) x

中文:
定理 birkhoffSum_of_comp_eq
  条件: {f : α -> α} {φ : α -> M} (h : φ ∘ f = φ) (n : 自然数)
  证明: by
  funext x
  suffices forall k, φ (f^[k] x) = φ x by simp [birkhoffSum, this]
  intro k
  exact congrFun (iterate_invariant h k) x

Depends on / 依赖: birkhoffSum, iterate_invariant
-/
theorem birkhoffSum_of_comp_eq {f : α -> α} {φ : α -> M} (h : φ ∘ f = φ) (n : Nat) :
    birkhoffSum f φ n = n • φ := by
  funext x
  suffices forall k, φ (f^[k] x) = φ x by simp [birkhoffSum, this]
  intro k
  exact congrFun (iterate_invariant h k) x

end AddCommMonoid

section AddCommGroup

variable {α G : Type*} [AddCommGroup G]

/--
theorem `birkhoffSum_neg` / 定理 `birkhoffSum_neg`

English:
theorem birkhoffSum_neg
  given: (f : α -> α) (g : α -> G) (n : Nat) (x : α)
  proof: by
  simp [birkhoffSum]

中文:
定理 birkhoffSum_neg
  条件: (f : α -> α) (g : α -> G) (n : 自然数) (x : α)
  证明: by
  simp [birkhoffSum]

Depends on / 依赖: birkhoffSum
-/
theorem birkhoffSum_neg (f : α -> α) (g : α -> G) (n : Nat) (x : α) :
    birkhoffSum f (-g) n x = -birkhoffSum f g n x := by
  simp [birkhoffSum]

/--
theorem `birkhoffSum_sub` / 定理 `birkhoffSum_sub`

English:
theorem birkhoffSum_sub
  given: (f : α -> α) (g g' : α -> G) (n : Nat) (x : α)
  proof: by
  simp [birkhoffSum]

中文:
定理 birkhoffSum_sub
  条件: (f : α -> α) (g g' : α -> G) (n : 自然数) (x : α)
  证明: by
  simp [birkhoffSum]

Depends on / 依赖: birkhoffSum
-/
theorem birkhoffSum_sub (f : α -> α) (g g' : α -> G) (n : Nat) (x : α) :
    birkhoffSum f (g - g') n x = birkhoffSum f g n x - birkhoffSum f g' n x := by
  simp [birkhoffSum]

/--
theorem `birkhoffSum_apply_sub_birkhoffSum` / 定理 `birkhoffSum_apply_sub_birkhoffSum`

English:
theorem birkhoffSum_apply_sub_birkhoffSum
  given: (f : α -> α) (g : α -> G) (n : Nat) (x : α)
  proof: by
  rw [← sub_eq_iff_eq_add.2 (birkhoffSum_succ f g n x)]; rw [← sub_eq_iff_eq_add.2 (birkhoffSum_succ' f g n x)]; rw [← sub_add]; rw [← sub_add]; rw [sub_add_comm]

中文:
定理 birkhoffSum_apply_sub_birkhoffSum
  条件: (f : α -> α) (g : α -> G) (n : 自然数) (x : α)
  证明: by
  rw [← sub_eq_iff_eq_add.2 (birkhoffSum_succ f g n x)]; rw [← sub_eq_iff_eq_add.2 (birkhoffSum_succ' f g n x)]; rw [← sub_add]; rw [← sub_add]; rw [sub_add_comm]

Depends on / 依赖: birkhoffSum_succ, sub_add, sub_add_comm, sub_eq_iff_eq_add
-/
theorem birkhoffSum_apply_sub_birkhoffSum (f : α -> α) (g : α -> G) (n : Nat) (x : α) :
    birkhoffSum f g n (f x) - birkhoffSum f g n x = g (f^[n] x) - g x := by
  rw [← sub_eq_iff_eq_add.2 (birkhoffSum_succ f g n x)]; rw [← sub_eq_iff_eq_add.2 (birkhoffSum_succ' f g n x)]; rw [← sub_add]; rw [← sub_add]; rw [sub_add_comm]

end AddCommGroup
