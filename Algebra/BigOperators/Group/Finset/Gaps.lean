/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
module

public import Mathlib.Order.Interval.Finset.Gaps
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
/-!
# Sum of gaps

This file proves that given a function `g` on `[a, b]`, `g b - g a` can be split according to a
given finite collection of pairwise disjoint closed subintervals of `[a, b]`. It is the sum of two
terms:
- the sum of `g y - g x` for `[x, y]` in the collection,
- the sum of `g y - g x` for `[x, y]` in the complement (modulo endpoints) of the union of the
  collection in `[a, b]`.

We use `Finset.intervalGapsWithin` to encode the complement.

We provide the multiplication versions in `Finset.prod_intervalGapsWithin_mul_prod_eq_div`,
`Finset.prod_intervalGapsWithin_eq_div_div_prod`, and the additive versions in
`Finset.sum_intervalGapsWithin_add_sum_eq_sub`, `Finset.sum_intervalGapsWithin_eq_sub_sub_sum`.

Technically, we don't require pairwise disjointness or endpoints to be within `[a, b]` or even
require that `a ≤ b`, but it makes the most sense if they are actually satisfied.
-/

public section

open Fin Fin.NatCast

variable {α β : Type*} [LinearOrder α] [CommGroup β]
  (F : Finset (α × α)) {k : Nat} (h : F.card = k) {a b : α}
  (g : α -> β)

@[to_additive]
/--
theorem `Finset.prod_eq_prod_range_intervalGapsWithin` / 定理 `Finset.prod_eq_prod_range_intervalGapsWithin`

English:
theorem Finset.prod_eq_prod_range_intervalGapsWithin
  given: (f : α -> α -> β)
  proof: by
  set p := F.intervalGapsWithin h a b
  symm
  apply prod_bij (fun (i : Nat) hi => ((p i).2, (p i.succ).1))
  · exact fun i _ => F.intervalGapsWithin_mapsTo h a b (x := i) (by grind)
  · intro i hi j hj hij
    rw [mem_range] at hi hj
    apply F.intervalGapsWithin_injOn h a b <;> grind
  · intro

中文:
定理 Finset.prod_eq_prod_range_intervalGapsWithin
  条件: (f : α -> α -> β)
  证明: by
  set p := F.intervalGapsWithin h a b
  symm
  apply prod_bij (fun (i : Nat) hi => ((p i).2, (p i.succ).1))
  · exact fun i _ => F.intervalGapsWithin_mapsTo h a b (x := i) (by grind)
  · intro i hi j hj hij
    rw [mem_range] at hi hj
    apply F.intervalGapsWithin_injOn h a b <;> grind
  · intro

Depends on / 依赖: F.intervalGapsWithin, F.intervalGapsWithin_injOn, F.intervalGapsWithin_mapsTo, F.intervalGapsWithin_surjOn, i.succ, intervalGapsWithin, intervalGapsWithin_injOn, intervalGapsWithin_mapsTo, intervalGapsWithin_surjOn, mem_range, prod_bij
-/
theorem Finset.prod_eq_prod_range_intervalGapsWithin (f : α -> α -> β) :
    ∏ z in F, f z.1 z.2 = ∏ i in range k,
      f (F.intervalGapsWithin h a b i).2 (F.intervalGapsWithin h a b i.succ).1 := by
  set p := F.intervalGapsWithin h a b
  symm
  apply prod_bij (fun (i : Nat) hi => ((p i).2, (p i.succ).1))
  · exact fun i _ => F.intervalGapsWithin_mapsTo h a b (x := i) (by grind)
  · intro i hi j hj hij
    rw [mem_range] at hi hj
    apply F.intervalGapsWithin_injOn h a b <;> grind
  · intro z hz
    obtain ⟨i, hi₁, hi₂⟩ := F.intervalGapsWithin_surjOn h a b hz
    exact ⟨i, by grind, hi₂⟩
  · simp

@[to_additive]
/--
theorem `Finset.prod_intervalGapsWithin_mul_prod_eq_div` / 定理 `Finset.prod_intervalGapsWithin_mul_prod_eq_div`

English:
theorem Finset.prod_intervalGapsWithin_mul_prod_eq_div
  proof: by
  rw [F.prod_eq_prod_range_intervalGapsWithin h (fun x y => g y / g x)]; rw [mul_comm]; rw [prod_range_succ]; rw [← mul_assoc]; rw [← prod_mul_distrib]; rw [prod_congr rfl (fun _ _ => div_mul_div_cancel _ _ _)]; rw [prod_range_div (fun i => g (F.intervalGapsWithin h a b i).1)]
  simp

@[to_additi

中文:
定理 Finset.prod_intervalGapsWithin_mul_prod_eq_div
  证明: by
  rw [F.prod_eq_prod_range_intervalGapsWithin h (fun x y => g y / g x)]; rw [mul_comm]; rw [prod_range_succ]; rw [← mul_assoc]; rw [← prod_mul_distrib]; rw [prod_congr rfl (fun _ _ => div_mul_div_cancel _ _ _)]; rw [prod_range_div (fun i => g (F.intervalGapsWithin h a b i).1)]
  simp

@[to_additi

Depends on / 依赖: F.intervalGapsWithin, F.prod_eq_prod_range_intervalGapsWithin, div_mul_div_cancel, intervalGapsWithin, mul_assoc, mul_comm, prod_congr, prod_eq_prod_range_intervalGapsWithin, prod_mul_distrib, prod_range_div, prod_range_succ
-/
theorem Finset.prod_intervalGapsWithin_mul_prod_eq_div :
    (∏ i in Finset.range (k + 1),
      g (F.intervalGapsWithin h a b i).2 / g (F.intervalGapsWithin h a b i).1) *
      ∏ z in F, g z.2 / g z.1 = g b / g a := by
  rw [F.prod_eq_prod_range_intervalGapsWithin h (fun x y => g y / g x)]; rw [mul_comm]; rw [prod_range_succ]; rw [← mul_assoc]; rw [← prod_mul_distrib]; rw [prod_congr rfl (fun _ _ => div_mul_div_cancel _ _ _)]; rw [prod_range_div (fun i => g (F.intervalGapsWithin h a b i).1)]
  simp

@[to_additive]
/--
theorem `Finset.prod_intervalGapsWithin_eq_div_div_prod` / 定理 `Finset.prod_intervalGapsWithin_eq_div_div_prod`

English:
theorem Finset.prod_intervalGapsWithin_eq_div_div_prod
  proof: eq_div_iff_mul_eq'.mpr (F.prod_intervalGapsWithin_mul_prod_eq_div h g)

中文:
定理 Finset.prod_intervalGapsWithin_eq_div_div_prod
  证明: eq_div_iff_mul_eq'.mpr (F.prod_intervalGapsWithin_mul_prod_eq_div h g)

Depends on / 依赖: F.prod_intervalGapsWithin_mul_prod_eq_div, eq_div_iff_mul_eq, prod_intervalGapsWithin_mul_prod_eq_div
-/
theorem Finset.prod_intervalGapsWithin_eq_div_div_prod :
    (∏ i in Finset.range (k + 1),
      g (F.intervalGapsWithin h a b i).2 / g (F.intervalGapsWithin h a b i).1) =
    (g b / g a) / ∏ z in F, g z.2 / g z.1 :=
  eq_div_iff_mul_eq'.mpr (F.prod_intervalGapsWithin_mul_prod_eq_div h g)
