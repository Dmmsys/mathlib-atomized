/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Big operators for `NatAntidiagonal`

This file contains theorems relevant to big operators over `Finset.NatAntidiagonal`.
-/

public section

variable {M N : Type*} [CommMonoid M] [AddCommMonoid N]

namespace Finset

open HasAntidiagonal

namespace Nat

/--
theorem `prod_antidiagonal_succ` / 定理 `prod_antidiagonal_succ`

English:
theorem prod_antidiagonal_succ
  given: {n : Nat} {f : Nat × Nat -> M}
  proof: by
  rw [antidiagonal_succ]; rw [prod_cons]; rw [prod_map]; rfl

中文:
定理 prod_antidiagonal_succ
  条件: {n : 自然数} {f : 自然数 × 自然数 -> M}
  证明: by
  rw [antidiagonal_succ]; rw [prod_cons]; rw [prod_map]; rfl

Depends on / 依赖: antidiagonal_succ, prod_cons, prod_map
-/
theorem prod_antidiagonal_succ {n : Nat} {f : Nat × Nat -> M} :
    (∏ p in antidiagonal (n + 1), f p)
      = f (0, n + 1) * ∏ p in antidiagonal n, f (p.1 + 1, p.2) := by
  rw [antidiagonal_succ]; rw [prod_cons]; rw [prod_map]; rfl

/--
theorem `sum_antidiagonal_succ` / 定理 `sum_antidiagonal_succ`

English:
theorem sum_antidiagonal_succ
  given: {n : Nat} {f : Nat × Nat -> N}
  proof: @prod_antidiagonal_succ (Multiplicative N) _ _ _

@[to_additive]

中文:
定理 sum_antidiagonal_succ
  条件: {n : 自然数} {f : 自然数 × 自然数 -> N}
  证明: @prod_antidiagonal_succ (Multiplicative N) _ _ _

@[to_additive]

Depends on / 依赖: Multiplicative, prod_antidiagonal_succ
-/
theorem sum_antidiagonal_succ {n : Nat} {f : Nat × Nat -> N} :
    (∑ p in antidiagonal (n + 1), f p) = f (0, n + 1) + ∑ p in antidiagonal n, f (p.1 + 1, p.2) :=
  @prod_antidiagonal_succ (Multiplicative N) _ _ _

@[to_additive]
/--
theorem `prod_antidiagonal_swap` / 定理 `prod_antidiagonal_swap`

English:
theorem prod_antidiagonal_swap
  given: {n : Nat} {f : Nat × Nat -> M}
  proof: by
  conv_lhs => rw [← map_swap_antidiagonal, Finset.prod_map]
  rfl

中文:
定理 prod_antidiagonal_swap
  条件: {n : 自然数} {f : 自然数 × 自然数 -> M}
  证明: by
  conv_lhs => rw [← map_swap_antidiagonal, Finset.prod_map]
  rfl

Depends on / 依赖: Finset, Finset.prod_map, conv_lhs, map_swap_antidiagonal, prod_map
-/
theorem prod_antidiagonal_swap {n : Nat} {f : Nat × Nat -> M} :
    ∏ p in antidiagonal n, f p.swap = ∏ p in antidiagonal n, f p := by
  conv_lhs => rw [← map_swap_antidiagonal, Finset.prod_map]
  rfl

/--
theorem `prod_antidiagonal_succ'` / 定理 `prod_antidiagonal_succ'`

English:
theorem prod_antidiagonal_succ'
  given: {n : Nat} {f : Nat × Nat -> M}
  statement: (∏ p in antidiagonal (n + 1), f p) =
  proof: by
  rw [← prod_antidiagonal_swap]; rw [prod_antidiagonal_succ]; rw [← prod_antidiagonal_swap]
  rfl

中文:
定理 prod_antidiagonal_succ'
  条件: {n : 自然数} {f : 自然数 × 自然数 -> M}
  结论: (∏ p in antidiagonal (n + 1), f p) =
  证明: by
  rw [← prod_antidiagonal_swap]; rw [prod_antidiagonal_succ]; rw [← prod_antidiagonal_swap]
  rfl

Depends on / 依赖: prod_antidiagonal_succ, prod_antidiagonal_swap
-/
theorem prod_antidiagonal_succ' {n : Nat} {f : Nat × Nat -> M} : (∏ p in antidiagonal (n + 1), f p) =
    f (n + 1, 0) * ∏ p in antidiagonal n, f (p.1, p.2 + 1) := by
  rw [← prod_antidiagonal_swap]; rw [prod_antidiagonal_succ]; rw [← prod_antidiagonal_swap]
  rfl

/--
theorem `sum_antidiagonal_succ'` / 定理 `sum_antidiagonal_succ'`

English:
theorem sum_antidiagonal_succ'
  given: {n : Nat} {f : Nat × Nat -> N}
  proof: @prod_antidiagonal_succ' (Multiplicative N) _ _ _

@[to_additive]

中文:
定理 sum_antidiagonal_succ'
  条件: {n : 自然数} {f : 自然数 × 自然数 -> N}
  证明: @prod_antidiagonal_succ' (Multiplicative N) _ _ _

@[to_additive]

Depends on / 依赖: Multiplicative, prod_antidiagonal_succ
-/
theorem sum_antidiagonal_succ' {n : Nat} {f : Nat × Nat -> N} :
    (∑ p in antidiagonal (n + 1), f p) = f (n + 1, 0) + ∑ p in antidiagonal n, f (p.1, p.2 + 1) :=
  @prod_antidiagonal_succ' (Multiplicative N) _ _ _

@[to_additive]
/--
theorem `prod_antidiagonal_subst` / 定理 `prod_antidiagonal_subst`

English:
theorem prod_antidiagonal_subst
  given: {n : Nat} {f : Nat × Nat -> Nat -> M}
  proof: prod_congr rfl fun p hp => by rw [mem_antidiagonal.mp hp]

@[to_additive]

中文:
定理 prod_antidiagonal_subst
  条件: {n : 自然数} {f : 自然数 × 自然数 -> 自然数 -> M}
  证明: prod_congr rfl fun p hp => by rw [mem_antidiagonal.mp hp]

@[to_additive]

Depends on / 依赖: mem_antidiagonal, mem_antidiagonal.mp, prod_congr
-/
theorem prod_antidiagonal_subst {n : Nat} {f : Nat × Nat -> Nat -> M} :
    ∏ p in antidiagonal n, f p n = ∏ p in antidiagonal n, f p (p.1 + p.2) :=
  prod_congr rfl fun p hp => by rw [mem_antidiagonal.mp hp]

@[to_additive]
/--
theorem `prod_antidiagonal_eq_prod_range_succ_mk` / 定理 `prod_antidiagonal_eq_prod_range_succ_mk`

English:
theorem prod_antidiagonal_eq_prod_range_succ_mk
  statement: {M : Type*} [CommMonoid M] (f : Nat × Nat -> M)
  proof: Finset.prod_map (range n.succ) ⟨fun i => (i, n - i), fun _ _ h => (Prod.mk.inj h).1⟩ f

中文:
定理 prod_antidiagonal_eq_prod_range_succ_mk
  结论: {M : 类型} [交换幺半群 M] (f : 自然数 × 自然数 -> M)
  证明: Finset.prod_map (range n.succ) ⟨fun i => (i, n - i), fun _ _ h => (Prod.mk.inj h).1⟩ f

Depends on / 依赖: Finset, Finset.prod_map, Prod.mk.inj, n.succ, prod_map
-/
theorem prod_antidiagonal_eq_prod_range_succ_mk {M : Type*} [CommMonoid M] (f : Nat × Nat -> M)
    (n : Nat) : ∏ ij in antidiagonal n, f ij = ∏ k in range n.succ, f (k, n - k) :=
  Finset.prod_map (range n.succ) ⟨fun i => (i, n - i), fun _ _ h => (Prod.mk.inj h).1⟩ f

/-- This lemma matches more generally than `Finset.Nat.prod_antidiagonal_eq_prod_range_succ_mk` when
using `rw ← `. -/
@[to_additive /-- This lemma matches more generally than
`Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk` when using `rw ← `. -/]
/--
theorem `prod_antidiagonal_eq_prod_range_succ` / 定理 `prod_antidiagonal_eq_prod_range_succ`

English:
theorem prod_antidiagonal_eq_prod_range_succ
  given: {M : Type*} [CommMonoid M] (f : Nat -> Nat -> M) (n : Nat)
  proof: prod_antidiagonal_eq_prod_range_succ_mk _ _

中文:
定理 prod_antidiagonal_eq_prod_range_succ
  条件: {M : 类型} [交换幺半群 M] (f : 自然数 -> 自然数 -> M) (n : 自然数)
  证明: prod_antidiagonal_eq_prod_range_succ_mk _ _

Depends on / 依赖: prod_antidiagonal_eq_prod_range_succ_mk
-/
theorem prod_antidiagonal_eq_prod_range_succ {M : Type*} [CommMonoid M] (f : Nat -> Nat -> M) (n : Nat) :
    ∏ ij in antidiagonal n, f ij.1 ij.2 = ∏ k in range n.succ, f k (n - k) :=
  prod_antidiagonal_eq_prod_range_succ_mk _ _
end Nat

end Finset
