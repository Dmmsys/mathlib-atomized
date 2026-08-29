/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Evaluation of polynomials in subrings

## Main results

* `mem_map_rangeS`, `mem_map_range`: the range of `mapRingHom f` consists of
  polynomials with coefficients in the range of `f`

-/

public section

namespace Polynomial

universe u v w y

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : Nat}

variable [Semiring R] {p q r : R[X]} [Semiring S]
variable (f : R ->+* S)

/--
theorem `mem_map_rangeS` / 定理 `mem_map_rangeS`

English:
theorem mem_map_rangeS
  given: {p : S[X]}
  statement: p in (mapRingHom f).rangeS ↔ forall n, p.coeff n in f.rangeS
  proof: by
  constructor
  · rintro ⟨p, rfl⟩ n
    rw [coe_mapRingHom]; rw [coeff_map]
    exact Set.mem_range_self _
  · intro h
    rw [p.as_sum_range_C_mul_X_pow]
    refine (mapRingHom f).rangeS.sum_mem ?_
    intro i _hi
    rcases h i with ⟨c, hc⟩
    use C c * X ^ i
    rw [coe_mapRingHom]; rw [Polyn

中文:
定理 mem_map_rangeS
  条件: {p : S[X]}
  结论: p in (mapRingHom f).rangeS ↔ 对任意 n, p.coeff n in f.rangeS
  证明: by
  constructor
  · rintro ⟨p, rfl⟩ n
    rw [coe_mapRingHom]; rw [coeff_map]
    exact Set.mem_range_self _
  · intro h
    rw [p.as_sum_range_C_mul_X_pow]
    refine (mapRingHom f).rangeS.sum_mem ?_
    intro i _hi
    rcases h i with ⟨c, hc⟩
    use C c * X ^ i
    rw [coe_mapRingHom]; rw [Polyn

Depends on / 依赖: Polynomial, Polynomial.map_mul, Polynomial.map_pow, Set.mem_range_self, as_sum_range_C_mul_X_pow, coe_mapRingHom, coeff_map, mapRingHom, map_C, map_X, map_mul, map_pow, mem_range_self, p.as_sum_range_C_mul_X_pow, rangeS, rangeS.sum_mem, sum_mem
-/
theorem mem_map_rangeS {p : S[X]} : p in (mapRingHom f).rangeS ↔ forall n, p.coeff n in f.rangeS := by
  constructor
  · rintro ⟨p, rfl⟩ n
    rw [coe_mapRingHom]; rw [coeff_map]
    exact Set.mem_range_self _
  · intro h
    rw [p.as_sum_range_C_mul_X_pow]
    refine (mapRingHom f).rangeS.sum_mem ?_
    intro i _hi
    rcases h i with ⟨c, hc⟩
    use C c * X ^ i
    rw [coe_mapRingHom]; rw [Polynomial.map_mul]; rw [map_C]; rw [hc]; rw [Polynomial.map_pow]; rw [map_X]

/--
theorem `notMem_map_rangeS` / 定理 `notMem_map_rangeS`

English:
theorem notMem_map_rangeS
  given: {p : S[X]}
  statement: p ∉ (mapRingHom f).rangeS ↔ exists n, p.coeff n ∉ f.rangeS
  proof: (mem_map_rangeS f (p := p)).not.trans not_forall

中文:
定理 notMem_map_rangeS
  条件: {p : S[X]}
  结论: p ∉ (mapRingHom f).rangeS ↔ 存在 n, p.coeff n ∉ f.rangeS
  证明: (mem_map_rangeS f (p := p)).not.trans not_forall

Depends on / 依赖: mem_map_rangeS, not.trans, not_forall
-/
theorem notMem_map_rangeS {p : S[X]} : p ∉ (mapRingHom f).rangeS ↔ exists n, p.coeff n ∉ f.rangeS :=
  (mem_map_rangeS f (p := p)).not.trans not_forall

/--
theorem `mem_map_range` / 定理 `mem_map_range`

English:
theorem mem_map_range
  given: {R S : Type*} [Ring R] [Ring S] (f : R ->+* S) {p : S[X]}
  proof: mem_map_rangeS f

中文:
定理 mem_map_range
  条件: {R S : 类型} [Ring R] [Ring S] (f : R ->+* S) {p : S[X]}
  证明: mem_map_rangeS f

Depends on / 依赖: mem_map_rangeS
-/
theorem mem_map_range {R S : Type*} [Ring R] [Ring S] (f : R ->+* S) {p : S[X]} :
    p in (mapRingHom f).range ↔ forall n, p.coeff n in f.range :=
  mem_map_rangeS f

/--
theorem `notMem_map_range` / 定理 `notMem_map_range`

English:
theorem notMem_map_range
  given: {R S : Type*} [Ring R] [Ring S] (f : R ->+* S) {p : S[X]}
  proof: notMem_map_rangeS f

中文:
定理 notMem_map_range
  条件: {R S : 类型} [Ring R] [Ring S] (f : R ->+* S) {p : S[X]}
  证明: notMem_map_rangeS f

Depends on / 依赖: notMem_map_rangeS
-/
theorem notMem_map_range {R S : Type*} [Ring R] [Ring S] (f : R ->+* S) {p : S[X]} :
    p ∉ (mapRingHom f).range ↔ exists n, p.coeff n ∉ f.range :=
  notMem_map_rangeS f

end Polynomial
