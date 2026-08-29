/-
Copyright (c) 2025 Alastair Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alastair Irving, Terry Tao, Ruben Van de Velde
-/
module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.Primorial
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.Data.Nat.Prime.Int

/-!
# Chebyshev functions

This file defines the Chebyshev functions `theta` and `psi`.
These give logarithmically weighted sums of primes and prime powers.

## Main definitions

- `Chebyshev.psi` gives the sum of `ArithmeticFunction.vonMangoldt`
- `Chebyshev.theta` gives the sum of `log p` over primes
- `Chebyshev.lcmUpto n` gives the least common multiple of `{1,...,n}`

## Main results

- `Chebyshev.theta_eq_log_primorial` shows that `θ x` is the log of the product of primes up to x
- `Chebyshev.theta_le_log4_mul_x` gives Chebyshev's upper bound on `θ`
- `Chebyshev.theta_ge` gives Chebyshev's lower bound on `θ`.
- `Chebyshev.psi_eq_log_lcmUpto` shows that `ψ n` is the log of the lcm of `{1,...,n}`.
- `Chebyshev.psi_eq_sum_theta` and `Chebyshev.psi_eq_theta_add_sum_theta` relate `ψ` to `θ`.
- `Chebyshev.psi_sub_theta_le_mul_sqrt` gives an upper bound on `ψ - θ`.
- `Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi` and
   `Chebyshev.psi_sub_theta_ge_psi_add_psi_add_psi` establish the Costa-Pereira inequalities
   for `ψ - θ`.
- `Chebyshev.psi_le_const_mul_self` gives Chebyshev's upper bound on `ψ`.
- `Chebyshev.psi_ge` gives Chebyshev's lower bound on `ψ`.
- `Chebyshev.primeCounting_eq_theta_div_log_add_integral` relates the prime counting function to `θ`
- `Chebyshev.eventually_primeCounting_le` gives an asymptotic upper bound on the
  prime counting function.
- `Chebyshev.pi_le_log4_mul_div` gives an explicit upper bound on the prime counting function.
- `Chebyshev.pi_ge` gives an explicit lower bound on the prime counting function.

## Notation

We introduce the scoped notations `θ` and `ψ` in the Chebyshev namespace for the Chebyshev
functions.

## References

Parts of this file were upstreamed from the PrimeNumberTheoremAnd project by Kontorovich et al, https://github.com/alexKontorovich/PrimeNumberTheoremAnd.

-/

@[expose] public section

open Nat hiding log
open Finset Real
open ArithmeticFunction hiding log id
open scoped Nat.Prime

namespace Chebyshev

/--
Definition of `psi` / `psi` 的定义

English:
definition psi
  signature: (x : Real)
  body: ∑ n in Ioc 0 ⌊x⌋₊, Λ n

@[inherit_doc]
scoped notation "ψ" => Chebyshev.psi

中文:
定义 psi
  签名: (x : 实数)
  定义体: ∑ n in Ioc 0 ⌊x⌋₊, Λ n

@[inherit_doc]
scoped notation "ψ" => Chebyshev.psi
-/
noncomputable def psi (x : Real) : Real :=
  ∑ n in Ioc 0 ⌊x⌋₊, Λ n

@[inherit_doc]
scoped notation "ψ" => Chebyshev.psi

/--
Definition of `theta` / `theta` 的定义

English:
definition theta
  signature: (x : Real)
  body: ∑ p in Ioc 0 ⌊x⌋₊ with p.Prime, log p

@[inherit_doc]
scoped notation "θ" => Chebyshev.theta

中文:
定义 theta
  签名: (x : 实数)
  定义体: ∑ p in Ioc 0 ⌊x⌋₊ with p.Prime, log p

@[inherit_doc]
scoped notation "θ" => Chebyshev.theta

Depends on / 依赖: p.Prime
-/
noncomputable def theta (x : Real) : Real :=
  ∑ p in Ioc 0 ⌊x⌋₊ with p.Prime, log p

@[inherit_doc]
scoped notation "θ" => Chebyshev.theta

/--
theorem `psi_nonneg` / 定理 `psi_nonneg`

English:
theorem psi_nonneg
  given: (x : Real)
  statement: 0 <= ψ x
  proof: sum_nonneg fun _ _ => (by simp)

中文:
定理 psi_nonneg
  条件: (x : 实数)
  结论: 0 <= ψ x
  证明: sum_nonneg fun _ _ => (by simp)

Depends on / 依赖: sum_nonneg
-/
theorem psi_nonneg (x : Real) : 0 <= ψ x := sum_nonneg fun _ _ => (by simp)

/--
theorem `theta_nonneg` / 定理 `theta_nonneg`

English:
theorem theta_nonneg
  given: (x : Real)
  statement: 0 <= θ x
  proof: sum_nonneg fun _ _ => log_nonneg (by aesop)

中文:
定理 theta_nonneg
  条件: (x : 实数)
  结论: 0 <= θ x
  证明: sum_nonneg fun _ _ => log_nonneg (by aesop)

Depends on / 依赖: log_nonneg, sum_nonneg
-/
theorem theta_nonneg (x : Real) : 0 <= θ x := sum_nonneg fun _ _ => log_nonneg (by aesop)

/--
theorem `theta_pos` / 定理 `theta_pos`

English:
theorem theta_pos
  given: {x : Real} (hy : 2 <= x)
  statement: 0 < θ x
  proof: by
  refine sum_pos (fun n hn => log_pos ?_) ⟨2, ?_⟩
  · simp only [mem_filter] at hn; exact_mod_cast hn.2.one_lt
  · have : 0 <= x := by grind
    simpa using ⟨(le_floor_iff this).2 hy, prime_two⟩

中文:
定理 theta_pos
  条件: {x : 实数} (hy : 2 <= x)
  结论: 0 < θ x
  证明: by
  refine sum_pos (fun n hn => log_pos ?_) ⟨2, ?_⟩
  · simp only [mem_filter] at hn; exact_mod_cast hn.2.one_lt
  · have : 0 <= x := by grind
    simpa using ⟨(le_floor_iff this).2 hy, prime_two⟩

Depends on / 依赖: le_floor_iff, log_pos, mem_filter, one_lt, prime_two, sum_pos
-/
theorem theta_pos {x : Real} (hy : 2 <= x) : 0 < θ x := by
  refine sum_pos (fun n hn => log_pos ?_) ⟨2, ?_⟩
  · simp only [mem_filter] at hn; exact_mod_cast hn.2.one_lt
  · have : 0 <= x := by grind
    simpa using ⟨(le_floor_iff this).2 hy, prime_two⟩

/--
theorem `psi_eq_sum_Icc` / 定理 `psi_eq_sum_Icc`

English:
theorem psi_eq_sum_Icc
  given: (x : Real)
  proof: by
  rw [psi]; rw [← add_sum_Ioc_eq_sum_Icc] <;> simp

中文:
定理 psi_eq_sum_Icc
  条件: (x : 实数)
  证明: by
  rw [psi]; rw [← add_sum_Ioc_eq_sum_Icc] <;> simp

Depends on / 依赖: add_sum_Ioc_eq_sum_Icc
-/
theorem psi_eq_sum_Icc (x : Real) :
    ψ x = ∑ n in Icc 0 ⌊x⌋₊, Λ n := by
  rw [psi]; rw [← add_sum_Ioc_eq_sum_Icc] <;> simp

/--
theorem `theta_eq_sum_Icc` / 定理 `theta_eq_sum_Icc`

English:
theorem theta_eq_sum_Icc
  given: (x : Real)
  proof: by
  rw [theta]; rw [sum_filter]; rw [sum_filter]; rw [← add_sum_Ioc_eq_sum_Icc] <;> simp

中文:
定理 theta_eq_sum_Icc
  条件: (x : 实数)
  证明: by
  rw [theta]; rw [sum_filter]; rw [sum_filter]; rw [← add_sum_Ioc_eq_sum_Icc] <;> simp

Depends on / 依赖: add_sum_Ioc_eq_sum_Icc, sum_filter
-/
theorem theta_eq_sum_Icc (x : Real) :
    θ x = ∑ p in Icc 0 ⌊x⌋₊ with p.Prime, log p := by
  rw [theta]; rw [sum_filter]; rw [sum_filter]; rw [← add_sum_Ioc_eq_sum_Icc] <;> simp

/--
theorem `theta_eq_sum_primesLE` / 定理 `theta_eq_sum_primesLE`

English:
theorem theta_eq_sum_primesLE
  given: (x : Real)
  proof: by
  simp [theta_eq_sum_Icc, primesLE_eq_filter_Icc_zero]

中文:
定理 theta_eq_sum_primesLE
  条件: (x : 实数)
  证明: by
  simp [theta_eq_sum_Icc, primesLE_eq_filter_Icc_zero]

Depends on / 依赖: primesLE_eq_filter_Icc_zero, theta_eq_sum_Icc
-/
theorem theta_eq_sum_primesLE (x : Real) :
    θ x = ∑ p in primesLE ⌊x⌋₊, log p := by
  simp [theta_eq_sum_Icc, primesLE_eq_filter_Icc_zero]

/--
theorem `theta_eq_sum_primesLE_log` / 定理 `theta_eq_sum_primesLE_log`

English:
theorem theta_eq_sum_primesLE_log
  given: (n : Nat)
  statement: θ n = ∑ p in primesLE n, log p
  proof: by
  simp [theta_eq_sum_primesLE]

中文:
定理 theta_eq_sum_primesLE_log
  条件: (n : 自然数)
  结论: θ n = ∑ p in primesLE n, log p
  证明: by
  simp [theta_eq_sum_primesLE]

Depends on / 依赖: theta_eq_sum_primesLE
-/
theorem theta_eq_sum_primesLE_log (n : Nat) : θ n = ∑ p in primesLE n, log p := by
  simp [theta_eq_sum_primesLE]

/--
theorem `psi_eq_zero_of_lt_two` / 定理 `psi_eq_zero_of_lt_two`

English:
theorem psi_eq_zero_of_lt_two
  given: {x : Real} (hx : x < 2)
  statement: ψ x = 0
  proof: by
  apply sum_eq_zero fun n hn => ?_
  simp only [mem_Ioc] at hn
  convert! vonMangoldt_apply_one
  have := lt_of_le_of_lt (le_floor_iff' hn.1.ne' |>.mp hn.2) hx
  norm_cast at this
  linarith

@[simp]

中文:
定理 psi_eq_zero_of_lt_two
  条件: {x : 实数} (hx : x < 2)
  结论: ψ x = 0
  证明: by
  apply sum_eq_zero fun n hn => ?_
  simp only [mem_Ioc] at hn
  convert! vonMangoldt_apply_one
  have := lt_of_le_of_lt (le_floor_iff' hn.1.ne' |>.mp hn.2) hx
  norm_cast at this
  linarith

@[simp]

Depends on / 依赖: convert, le_floor_iff, lt_of_le_of_lt, mem_Ioc, sum_eq_zero, vonMangoldt_apply_one
-/
theorem psi_eq_zero_of_lt_two {x : Real} (hx : x < 2) : ψ x = 0 := by
  apply sum_eq_zero fun n hn => ?_
  simp only [mem_Ioc] at hn
  convert! vonMangoldt_apply_one
  have := lt_of_le_of_lt (le_floor_iff' hn.1.ne' |>.mp hn.2) hx
  norm_cast at this
  linarith

@[simp]
/--
theorem `psi_eq_zero_iff` / 定理 `psi_eq_zero_iff`

English:
theorem psi_eq_zero_iff
  given: {x : Real}
  statement: ψ x = 0 ↔ x < 2
  proof: by
  refine ⟨fun h₀ => ?_, psi_eq_zero_of_lt_two⟩
  by_contra! contra
  replace contra : 2 in Ioc 0 ⌊x⌋₊ := by rw [mem_Ioc, le_floor_iff (by grind)]; grind
  have : Λ 2 <= ψ x := single_le_sum (fun n _ => vonMangoldt_nonneg (n := n)) contra
  have := vonMangoldt_pos_iff.mpr prime_two.isPrimePow
  li

中文:
定理 psi_eq_zero_iff
  条件: {x : 实数}
  结论: ψ x = 0 ↔ x < 2
  证明: by
  refine ⟨fun h₀ => ?_, psi_eq_zero_of_lt_two⟩
  by_contra! contra
  replace contra : 2 in Ioc 0 ⌊x⌋₊ := by rw [mem_Ioc, le_floor_iff (by grind)]; grind
  have : Λ 2 <= ψ x := single_le_sum (fun n _ => vonMangoldt_nonneg (n := n)) contra
  have := vonMangoldt_pos_iff.mpr prime_two.isPrimePow
  li

Depends on / 依赖: contra, isPrimePow, le_floor_iff, mem_Ioc, prime_two, prime_two.isPrimePow, psi_eq_zero_of_lt_two, replace, single_le_sum, vonMangoldt_nonneg, vonMangoldt_pos_iff, vonMangoldt_pos_iff.mpr
-/
theorem psi_eq_zero_iff {x : Real} : ψ x = 0 ↔ x < 2 := by
  refine ⟨fun h₀ => ?_, psi_eq_zero_of_lt_two⟩
  by_contra! contra
  replace contra : 2 in Ioc 0 ⌊x⌋₊ := by rw [mem_Ioc, le_floor_iff (by grind)]; grind
  have : Λ 2 <= ψ x := single_le_sum (fun n _ => vonMangoldt_nonneg (n := n)) contra
  have := vonMangoldt_pos_iff.mpr prime_two.isPrimePow
  linarith

/--
theorem `psi_eq_zero_of_le_one` / 定理 `psi_eq_zero_of_le_one`

English:
theorem psi_eq_zero_of_le_one
  given: {x : Real} (hx : x <= 1)
  statement: ψ x = 0
  proof: psi_eq_zero_of_lt_two (by linarith)

@[simp]

中文:
定理 psi_eq_zero_of_le_one
  条件: {x : 实数} (hx : x <= 1)
  结论: ψ x = 0
  证明: psi_eq_zero_of_lt_two (by linarith)

@[simp]

Depends on / 依赖: psi_eq_zero_of_lt_two
-/
theorem psi_eq_zero_of_le_one {x : Real} (hx : x <= 1) : ψ x = 0 :=
  psi_eq_zero_of_lt_two (by linarith)

@[simp]
/--
theorem `psi_zero` / 定理 `psi_zero`

English:
theorem psi_zero
  statement: ψ 0 = 0
  proof: psi_eq_zero_of_lt_two zero_lt_two

@[simp]

中文:
定理 psi_zero
  结论: ψ 0 = 0
  证明: psi_eq_zero_of_lt_two zero_lt_two

@[simp]

Depends on / 依赖: psi_eq_zero_of_lt_two, zero_lt_two
-/
theorem psi_zero : ψ 0 = 0 := psi_eq_zero_of_lt_two zero_lt_two

@[simp]
/--
theorem `psi_one` / 定理 `psi_one`

English:
theorem psi_one
  statement: ψ 1 = 0
  proof: psi_eq_zero_of_lt_two one_lt_two

中文:
定理 psi_one
  结论: ψ 1 = 0
  证明: psi_eq_zero_of_lt_two one_lt_two

Depends on / 依赖: one_lt_two, psi_eq_zero_of_lt_two
-/
theorem psi_one : ψ 1 = 0 := psi_eq_zero_of_lt_two one_lt_two

/--
theorem `theta_eq_zero_of_lt_two` / 定理 `theta_eq_zero_of_lt_two`

English:
theorem theta_eq_zero_of_lt_two
  given: {x : Real} (hx : x < 2)
  statement: θ x = 0
  proof: by
  apply sum_eq_zero fun n hn => ?_
  convert! log_one
  simp only [mem_filter, mem_Ioc] at hn
  have := lt_of_le_of_lt (le_floor_iff' hn.1.1.ne' |>.mp hn.1.2) hx
  norm_cast at ⊢ this
  linarith

@[simp]

中文:
定理 theta_eq_zero_of_lt_two
  条件: {x : 实数} (hx : x < 2)
  结论: θ x = 0
  证明: by
  apply sum_eq_zero fun n hn => ?_
  convert! log_one
  simp only [mem_filter, mem_Ioc] at hn
  have := lt_of_le_of_lt (le_floor_iff' hn.1.1.ne' |>.mp hn.1.2) hx
  norm_cast at ⊢ this
  linarith

@[simp]

Depends on / 依赖: convert, le_floor_iff, log_one, lt_of_le_of_lt, mem_Ioc, mem_filter, sum_eq_zero
-/
theorem theta_eq_zero_of_lt_two {x : Real} (hx : x < 2) : θ x = 0 := by
  apply sum_eq_zero fun n hn => ?_
  convert! log_one
  simp only [mem_filter, mem_Ioc] at hn
  have := lt_of_le_of_lt (le_floor_iff' hn.1.1.ne' |>.mp hn.1.2) hx
  norm_cast at ⊢ this
  linarith

@[simp]
/--
theorem `theta_eq_zero_iff` / 定理 `theta_eq_zero_iff`

English:
theorem theta_eq_zero_iff
  given: {x : Real}
  statement: θ x = 0 ↔ x < 2
  proof: by
  refine ⟨fun h₀ => ?_, theta_eq_zero_of_lt_two⟩
  by_contra! contra
  replace contra : 2 in Ioc 0 ⌊x⌋₊ := by rw [mem_Ioc, le_floor_iff (by grind)]; grind
  have h₁ : log (↑(2 : Nat) : Real) <= θ x :=
    single_le_sum (fun p hp => log_nonneg (by aesop)) (by aesop (add simp prime_two))
  have := 

中文:
定理 theta_eq_zero_iff
  条件: {x : 实数}
  结论: θ x = 0 ↔ x < 2
  证明: by
  refine ⟨fun h₀ => ?_, theta_eq_zero_of_lt_two⟩
  by_contra! contra
  replace contra : 2 in Ioc 0 ⌊x⌋₊ := by rw [mem_Ioc, le_floor_iff (by grind)]; grind
  have h₁ : log (↑(2 : Nat) : Real) <= θ x :=
    single_le_sum (fun p hp => log_nonneg (by aesop)) (by aesop (add simp prime_two))
  have := 

Depends on / 依赖: Real.log_pos, contra, le_floor_iff, log_nonneg, log_pos, mem_Ioc, one_lt_two, prime_two, replace, single_le_sum, theta_eq_zero_of_lt_two
-/
theorem theta_eq_zero_iff {x : Real} : θ x = 0 ↔ x < 2 := by
  refine ⟨fun h₀ => ?_, theta_eq_zero_of_lt_two⟩
  by_contra! contra
  replace contra : 2 in Ioc 0 ⌊x⌋₊ := by rw [mem_Ioc, le_floor_iff (by grind)]; grind
  have h₁ : log (↑(2 : Nat) : Real) <= θ x :=
    single_le_sum (fun p hp => log_nonneg (by aesop)) (by aesop (add simp prime_two))
  have := Real.log_pos one_lt_two
  grind

/--
theorem `theta_eq_zero_of_le_one` / 定理 `theta_eq_zero_of_le_one`

English:
theorem theta_eq_zero_of_le_one
  given: {x : Real} (hx : x <= 1)
  statement: θ x = 0
  proof: theta_eq_zero_of_lt_two (by linarith)

@[simp]

中文:
定理 theta_eq_zero_of_le_one
  条件: {x : 实数} (hx : x <= 1)
  结论: θ x = 0
  证明: theta_eq_zero_of_lt_two (by linarith)

@[simp]

Depends on / 依赖: theta_eq_zero_of_lt_two
-/
theorem theta_eq_zero_of_le_one {x : Real} (hx : x <= 1) : θ x = 0 :=
  theta_eq_zero_of_lt_two (by linarith)

@[simp]
/--
theorem `theta_zero` / 定理 `theta_zero`

English:
theorem theta_zero
  statement: θ 0 = 0
  proof: theta_eq_zero_of_lt_two zero_lt_two

@[simp]

中文:
定理 theta_zero
  结论: θ 0 = 0
  证明: theta_eq_zero_of_lt_two zero_lt_two

@[simp]

Depends on / 依赖: BoundedOrder, HeytingAlgebra, HeytingAlgebra.toBoundedOrder, theta_eq_zero_of_lt_two, toBoundedOrder, zero_lt_two
-/
theorem theta_zero : θ 0 = 0 := theta_eq_zero_of_lt_two zero_lt_two

@[simp]
/--
theorem `theta_one` / 定理 `theta_one`

English:
theorem theta_one
  statement: θ 1 = 0
  proof: theta_eq_zero_of_lt_two one_lt_two

中文:
定理 theta_one
  结论: θ 1 = 0
  证明: theta_eq_zero_of_lt_two one_lt_two

Depends on / 依赖: one_lt_two, theta_eq_zero_of_lt_two
-/
theorem theta_one : θ 1 = 0 := theta_eq_zero_of_lt_two one_lt_two

/--
theorem `psi_eq_psi_coe_floor` / 定理 `psi_eq_psi_coe_floor`

English:
theorem psi_eq_psi_coe_floor
  given: (x : Real)
  statement: ψ x = ψ ⌊x⌋₊
  proof: by
  unfold psi
  rw [floor_natCast]

中文:
定理 psi_eq_psi_coe_floor
  条件: (x : 实数)
  结论: ψ x = ψ ⌊x⌋₊
  证明: by
  unfold psi
  rw [floor_natCast]

Depends on / 依赖: floor_natCast
-/
theorem psi_eq_psi_coe_floor (x : Real) : ψ x = ψ ⌊x⌋₊ := by
  unfold psi
  rw [floor_natCast]

/--
theorem `theta_eq_theta_coe_floor` / 定理 `theta_eq_theta_coe_floor`

English:
theorem theta_eq_theta_coe_floor
  given: (x : Real)
  statement: θ x = θ ⌊x⌋₊
  proof: by
  unfold theta
  rw [floor_natCast]

@[gcongr]

中文:
定理 theta_eq_theta_coe_floor
  条件: (x : 实数)
  结论: θ x = θ ⌊x⌋₊
  证明: by
  unfold theta
  rw [floor_natCast]

@[gcongr]

Depends on / 依赖: floor_natCast
-/
theorem theta_eq_theta_coe_floor (x : Real) : θ x = θ ⌊x⌋₊ := by
  unfold theta
  rw [floor_natCast]

@[gcongr]
/--
theorem `psi_mono` / 定理 `psi_mono`

English:
theorem psi_mono
  statement: Monotone ψ
  proof: by
  intro x y hxy
  apply sum_le_sum_of_subset_of_nonneg
  · exact Ioc_subset_Ioc (by rfl) (by gcongr)
  · simp

@[gcongr]

中文:
定理 psi_mono
  结论: Monotone ψ
  证明: by
  intro x y hxy
  apply sum_le_sum_of_subset_of_nonneg
  · exact Ioc_subset_Ioc (by rfl) (by gcongr)
  · simp

@[gcongr]

Depends on / 依赖: Ioc_subset_Ioc, sum_le_sum_of_subset_of_nonneg
-/
theorem psi_mono : Monotone ψ := by
  intro x y hxy
  apply sum_le_sum_of_subset_of_nonneg
  · exact Ioc_subset_Ioc (by rfl) (by gcongr)
  · simp

@[gcongr]
/--
theorem `theta_mono` / 定理 `theta_mono`

English:
theorem theta_mono
  statement: Monotone θ
  proof: by
  intro x y hxy
  apply sum_le_sum_of_subset_of_nonneg
· exact filter_subset_filter _ Ioc_subset_Ioc_right (by gcongr)
  · exact fun p _ _ => log_natCast_nonneg p

中文:
定理 theta_mono
  结论: Monotone θ
  证明: by
  intro x y hxy
  apply sum_le_sum_of_subset_of_nonneg
· exact filter_subset_filter _ Ioc_subset_Ioc_right (by gcongr)
  · exact fun p _ _ => log_natCast_nonneg p

Depends on / 依赖: Ioc_subset_Ioc_right, filter_subset_filter, log_natCast_nonneg, sum_le_sum_of_subset_of_nonneg
-/
theorem theta_mono : Monotone θ := by
  intro x y hxy
  apply sum_le_sum_of_subset_of_nonneg
· exact filter_subset_filter _ Ioc_subset_Ioc_right (by gcongr)
  · exact fun p _ _ => log_natCast_nonneg p

/--
theorem `theta_eq_log_primorial` / 定理 `theta_eq_log_primorial`

English:
theorem theta_eq_log_primorial
  given: (x : Real)
  statement: θ x = log (primorial ⌊x⌋₊)
  proof: by
  unfold theta primorial
  rw [cast_prod]; rw [log_prod (fun p hp => mod_cast (mem_filter.mp hp).2.pos.ne')]
  congr 1 with p
  simp_all [Prime.pos]

中文:
定理 theta_eq_log_primorial
  条件: (x : 实数)
  结论: θ x = log (primorial ⌊x⌋₊)
  证明: by
  unfold theta primorial
  rw [cast_prod]; rw [log_prod (fun p hp => mod_cast (mem_filter.mp hp).2.pos.ne')]
  congr 1 with p
  simp_all [Prime.pos]

Depends on / 依赖: Prime.pos, cast_prod, log_prod, mem_filter, mem_filter.mp, mod_cast, pos.ne, primorial
-/
theorem theta_eq_log_primorial (x : Real) : θ x = log (primorial ⌊x⌋₊) := by
  unfold theta primorial
  rw [cast_prod]; rw [log_prod (fun p hp => mod_cast (mem_filter.mp hp).2.pos.ne')]
  congr 1 with p
  simp_all [Prime.pos]

/--
theorem `theta_le_log4_mul_x` / 定理 `theta_le_log4_mul_x`

English:
theorem theta_le_log4_mul_x
  given: {x : Real} (hx : 0 <= x)
  statement: θ x <= log 4 * x
  proof: by
  rw [theta_eq_log_primorial]
  trans log (4 ^ ⌊x⌋₊)
  · gcongr <;> norm_cast
    exacts [primorial_pos _, primorial_le_four_pow _]
  rw [Real.log_pow]; rw [mul_comm]
  gcongr
  exact floor_le hx

中文:
定理 theta_le_log4_mul_x
  条件: {x : 实数} (hx : 0 <= x)
  结论: θ x <= log 4 * x
  证明: by
  rw [theta_eq_log_primorial]
  trans log (4 ^ ⌊x⌋₊)
  · gcongr <;> norm_cast
    exacts [primorial_pos _, primorial_le_four_pow _]
  rw [Real.log_pow]; rw [mul_comm]
  gcongr
  exact floor_le hx

Depends on / 依赖: Real.log_pow, exacts, floor_le, log_pow, mul_comm, primorial_le_four_pow, primorial_pos, theta_eq_log_primorial
-/
theorem theta_le_log4_mul_x {x : Real} (hx : 0 <= x) : θ x <= log 4 * x := by
  rw [theta_eq_log_primorial]
  trans log (4 ^ ⌊x⌋₊)
  · gcongr <;> norm_cast
    exacts [primorial_pos _, primorial_le_four_pow _]
  rw [Real.log_pow]; rw [mul_comm]
  gcongr
  exact floor_le hx

end Chebyshev

namespace Nat
/-!
## Least common multiple of `{1,...,n}`

Basic facts about the least common multiple of the first `n` natural numbers
-/

/--
Definition of `lcmUpto` / `lcmUpto` 的定义

English:
definition lcmUpto
  signature: (n : Nat)
  body: (Icc 1 n).lcm id

中文:
定义 lcmUpto
  签名: (n : 自然数)
  定义体: (Icc 1 n).lcm id
-/
def lcmUpto (n : Nat) : Nat := (Icc 1 n).lcm id

/--
theorem `lcmUpto_ne_zero` / 定理 `lcmUpto_ne_zero`

English:
theorem lcmUpto_ne_zero
  given: (n : Nat)
  statement: lcmUpto n != 0
  proof: by simp [lcmUpto]

中文:
定理 lcmUpto_ne_zero
  条件: (n : 自然数)
  结论: lcmUpto n != 0
  证明: by simp [lcmUpto]

Depends on / 依赖: lcmUpto
-/
theorem lcmUpto_ne_zero (n : Nat) : lcmUpto n != 0 := by simp [lcmUpto]

/--
theorem `lcmUpto_pos` / 定理 `lcmUpto_pos`

English:
theorem lcmUpto_pos
  given: (n : Nat)
  statement: 0 < lcmUpto n
  proof: pos_of_ne_zero lcmUpto_ne_zero n

中文:
定理 lcmUpto_pos
  条件: (n : 自然数)
  结论: 0 < lcmUpto n
  证明: pos_of_ne_zero lcmUpto_ne_zero n

Depends on / 依赖: lcmUpto_ne_zero, pos_of_ne_zero
-/
theorem lcmUpto_pos (n : Nat) : 0 < lcmUpto n := pos_of_ne_zero lcmUpto_ne_zero n

/--
theorem `factorization_lcmUpto` / 定理 `factorization_lcmUpto`

English:
theorem factorization_lcmUpto
  given: (n : Nat) {p : Nat} (hp : p.Prime)
  proof: by
  rw [lcmUpto]; rw [Finset.factorization_lcm (fun _ _ => by grind)]
  have := hp.one_lt
  refine le_antisymm ?_ ?_
  · simp only [Finset.sup_le_iff, mem_Icc, and_imp]
    exact fun m _ h => le_log_of_pow_le this (le_of_dvd (by grind) (ordProj_dvd m p) |>.trans h)
  rcases le_or_gt p n with _ | h


中文:
定理 factorization_lcmUpto
  条件: (n : 自然数) {p : 自然数} (hp : p.Prime)
  证明: by
  rw [lcmUpto]; rw [Finset.factorization_lcm (fun _ _ => by grind)]
  have := hp.one_lt
  refine le_antisymm ?_ ?_
  · simp only [Finset.sup_le_iff, mem_Icc, and_imp]
    exact fun m _ h => le_log_of_pow_le this (le_of_dvd (by grind) (ordProj_dvd m p) |>.trans h)
  rcases le_or_gt p n with _ | h


Depends on / 依赖: Finset, Finset.factorization_lcm, Finset.sup_le_iff, and_imp, factorization_lcm, hp.one_lt, lcmUpto, le_antisymm, le_log_of_pow_le, le_of_dvd, le_or_gt, le_sup, log_of_lt, mem_Icc, one_lt, ordProj_dvd, p.log, pow_log_le_self, sup_le_iff
-/
theorem factorization_lcmUpto (n : Nat) {p : Nat} (hp : p.Prime) :
    (lcmUpto n).factorization p = p.log n := by
  rw [lcmUpto]; rw [Finset.factorization_lcm (fun _ _ => by grind)]
  have := hp.one_lt
  refine le_antisymm ?_ ?_
  · simp only [Finset.sup_le_iff, mem_Icc, and_imp]
    exact fun m _ h => le_log_of_pow_le this (le_of_dvd (by grind) (ordProj_dvd m p) |>.trans h)
  rcases le_or_gt p n with _ | h
  · have := pow_log_le_self p (x := n) (by linarith)
    grw [← le_sup (b := p ^ p.log n) (by grind)]
    simp [hp]
  simp [log_of_lt h]

/--
theorem `lcmUpto_dvd_factorial` / 定理 `lcmUpto_dvd_factorial`

English:
theorem lcmUpto_dvd_factorial
  given: (n : Nat)
  statement: lcmUpto n ∣ n !
  proof: by
  simp +contextual [lcmUpto, dvd_factorial, Order.one_le_iff_pos]

中文:
定理 lcmUpto_dvd_factorial
  条件: (n : 自然数)
  结论: lcmUpto n ∣ n !
  证明: by
  simp +contextual [lcmUpto, dvd_factorial, Order.one_le_iff_pos]

Depends on / 依赖: Order.one_le_iff_pos, contextual, dvd_factorial, lcmUpto, one_le_iff_pos
-/
theorem lcmUpto_dvd_factorial (n : Nat) : lcmUpto n ∣ n ! := by
  simp +contextual [lcmUpto, dvd_factorial, Order.one_le_iff_pos]

/--
theorem `primeFactors_lcmUpto` / 定理 `primeFactors_lcmUpto`

English:
theorem primeFactors_lcmUpto
  given: (n : Nat)
  statement: primeFactors (lcmUpto n) = primesLE n
  proof: by
  ext p
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := prime_of_mem_primeFactors h
    rw [← support_factorization]; rw [Finsupp.mem_support_iff]; rw [factorization_lcmUpto _ this] at h
    simp_all [mem_primesLE]
· refine Prime.mem_primeFactors (prime_of_mem_primesLE h) (dvd_lcm ?_) lcmUpto_ne_

中文:
定理 primeFactors_lcmUpto
  条件: (n : 自然数)
  结论: primeFactors (lcmUpto n) = primesLE n
  证明: by
  ext p
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := prime_of_mem_primeFactors h
    rw [← support_factorization]; rw [Finsupp.mem_support_iff]; rw [factorization_lcmUpto _ this] at h
    simp_all [mem_primesLE]
· refine Prime.mem_primeFactors (prime_of_mem_primesLE h) (dvd_lcm ?_) lcmUpto_ne_

Depends on / 依赖: Finsupp, Finsupp.mem_support_iff, Prime.mem_primeFactors, dvd_lcm, factorization_lcmUpto, lcmUpto_ne_zero, le_of_mem_primesLE, mem_Icc, mem_Icc.mpr, mem_primeFactors, mem_primesLE, mem_support_iff, one_le, prime_of_mem_primeFactors, prime_of_mem_primesLE, support_factorization
-/
theorem primeFactors_lcmUpto (n : Nat) : primeFactors (lcmUpto n) = primesLE n := by
  ext p
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := prime_of_mem_primeFactors h
    rw [← support_factorization]; rw [Finsupp.mem_support_iff]; rw [factorization_lcmUpto _ this] at h
    simp_all [mem_primesLE]
· refine Prime.mem_primeFactors (prime_of_mem_primesLE h) (dvd_lcm ?_) lcmUpto_ne_zero n
    exact mem_Icc.mpr ⟨(prime_of_mem_primesLE h).one_le, le_of_mem_primesLE h⟩

/--
theorem `primorial_dvd_lcmUpto` / 定理 `primorial_dvd_lcmUpto`

English:
theorem primorial_dvd_lcmUpto
  given: (n : Nat)
  statement: primorial n ∣ lcmUpto n
  proof: by
  simp only [primorial]
  rw [← primesLE_eq_filter_range]; rw [← primeFactors_lcmUpto]
  exact prod_primeFactors_dvd _

中文:
定理 primorial_dvd_lcmUpto
  条件: (n : 自然数)
  结论: primorial n ∣ lcmUpto n
  证明: by
  simp only [primorial]
  rw [← primesLE_eq_filter_range]; rw [← primeFactors_lcmUpto]
  exact prod_primeFactors_dvd _

Depends on / 依赖: primeFactors_lcmUpto, primesLE_eq_filter_range, primorial, prod_primeFactors_dvd
-/
theorem primorial_dvd_lcmUpto (n : Nat) : primorial n ∣ lcmUpto n := by
  simp only [primorial]
  rw [← primesLE_eq_filter_range]; rw [← primeFactors_lcmUpto]
  exact prod_primeFactors_dvd _

/--
theorem `lcmUpto_eq_prod` / 定理 `lcmUpto_eq_prod`

English:
theorem lcmUpto_eq_prod
  given: (n : Nat)
  proof: by
  conv_lhs => rw [← prod_factorization_pow_eq_self (lcmUpto_ne_zero n)]
  rw [prod_factorization_eq_prod_primeFactors]
  congr
  exact primeFactors_lcmUpto n

中文:
定理 lcmUpto_eq_prod
  条件: (n : 自然数)
  证明: by
  conv_lhs => rw [← prod_factorization_pow_eq_self (lcmUpto_ne_zero n)]
  rw [prod_factorization_eq_prod_primeFactors]
  congr
  exact primeFactors_lcmUpto n

Depends on / 依赖: conv_lhs, lcmUpto_ne_zero, primeFactors_lcmUpto, prod_factorization_eq_prod_primeFactors, prod_factorization_pow_eq_self
-/
theorem lcmUpto_eq_prod (n : Nat) :
    lcmUpto n = ∏ p in primesLE n, p ^ ((lcmUpto n).factorization p) := by
  conv_lhs => rw [← prod_factorization_pow_eq_self (lcmUpto_ne_zero n)]
  rw [prod_factorization_eq_prod_primeFactors]
  congr
  exact primeFactors_lcmUpto n

/--
theorem `lcmUpto_eq_prod_pow_log` / 定理 `lcmUpto_eq_prod_pow_log`

English:
theorem lcmUpto_eq_prod_pow_log
  given: (n : Nat)
  statement: lcmUpto n = ∏ p in primesLE n, p ^ p.log n
  proof: by
  rw [lcmUpto_eq_prod]
exact Finset.prod_congr rfl fun p hp => congrArg (p ^ ·)
factorization_lcmUpto n prime_of_mem_primesLE hp

中文:
定理 lcmUpto_eq_prod_pow_log
  条件: (n : 自然数)
  结论: lcmUpto n = ∏ p in primesLE n, p ^ p.log n
  证明: by
  rw [lcmUpto_eq_prod]
exact Finset.prod_congr rfl fun p hp => congrArg (p ^ ·)
factorization_lcmUpto n prime_of_mem_primesLE hp

Depends on / 依赖: Finset, Finset.prod_congr, factorization_lcmUpto, lcmUpto_eq_prod, prime_of_mem_primesLE, prod_congr
-/
theorem lcmUpto_eq_prod_pow_log (n : Nat) : lcmUpto n = ∏ p in primesLE n, p ^ p.log n := by
  rw [lcmUpto_eq_prod]
exact Finset.prod_congr rfl fun p hp => congrArg (p ^ ·)
factorization_lcmUpto n prime_of_mem_primesLE hp

/--
theorem `lcmUpto_eq_prod_pow_floor` / 定理 `lcmUpto_eq_prod_pow_floor`

English:
theorem lcmUpto_eq_prod_pow_floor
  given: (n : Nat)
  proof: by
  simp_rw [lcmUpto_eq_prod_pow_log, ← natFloor_logb_natCast, ← log_div_log]

中文:
定理 lcmUpto_eq_prod_pow_floor
  条件: (n : 自然数)
  证明: by
  simp_rw [lcmUpto_eq_prod_pow_log, ← natFloor_logb_natCast, ← log_div_log]

Depends on / 依赖: lcmUpto_eq_prod_pow_log, log_div_log, natFloor_logb_natCast, simp_rw
-/
theorem lcmUpto_eq_prod_pow_floor (n : Nat) :
    lcmUpto n = ∏ p in primesLE n, p ^ ⌊Real.log n / Real.log p⌋₊ := by
  simp_rw [lcmUpto_eq_prod_pow_log, ← natFloor_logb_natCast, ← log_div_log]

end Nat

namespace Chebyshev

/--
theorem `psi_eq_sum_mul_log_prime` / 定理 `psi_eq_sum_mul_log_prime`

English:
theorem psi_eq_sum_mul_log_prime
  given: (n : Nat)
  statement: ψ n = ∑ p in primesLE n, p.log n * log p
  proof: calc
  _ = ∑ m in Icc 1 n, Λ m := by simp [psi, ← Icc_add_one_left_eq_Ioc]
  _ = ∑ m in ((Icc 1 n).filter Prime).biUnion fun p => image (p ^ ·) (Icc 1 (p.log n)), Λ m := by
    refine (sum_subset (fun q hq => ?_) fun x hx => ?_).symm
    · simp only [mem_biUnion, mem_filter, mem_Icc, mem_image] at h

中文:
定理 psi_eq_sum_mul_log_prime
  条件: (n : 自然数)
  结论: ψ n = ∑ p in primesLE n, p.log n * log p
  证明: calc
  _ = ∑ m in Icc 1 n, Λ m := by simp [psi, ← Icc_add_one_left_eq_Ioc]
  _ = ∑ m in ((Icc 1 n).filter Prime).biUnion fun p => image (p ^ ·) (Icc 1 (p.log n)), Λ m := by
    refine (sum_subset (fun q hq => ?_) fun x hx => ?_).symm
    · simp only [mem_biUnion, mem_filter, mem_Icc, mem_image] at h
-/
theorem psi_eq_sum_mul_log_prime (n : Nat) : ψ n = ∑ p in primesLE n, p.log n * log p := calc
  _ = ∑ m in Icc 1 n, Λ m := by simp [psi, ← Icc_add_one_left_eq_Ioc]
  _ = ∑ m in ((Icc 1 n).filter Prime).biUnion fun p => image (p ^ ·) (Icc 1 (p.log n)), Λ m := by
    refine (sum_subset (fun q hq => ?_) fun x hx => ?_).symm
    · simp only [mem_biUnion, mem_filter, mem_Icc, mem_image] at hq ⊢
      obtain ⟨p, _, k, ⟨_, hk⟩, rfl⟩ := hq
      exact ⟨by grind, pow_le_of_le_log (by linarith) hk⟩
    · simp only [mem_biUnion, mem_filter, mem_Icc, mem_image, not_exists, not_and, and_imp,
        vonMangoldt_eq_zero_iff, isPrimePow_nat_iff]
      contrapose!
      rintro ⟨p, k, hp, hk, rfl⟩
      simp only [mem_Icc] at hx
      have hpn : p <= n := (le_of_dvd (by lia) (dvd_pow_self p hk.ne')).trans hx.2
      exact ⟨p, ⟨hp.one_le, hpn, hp, ⟨k, ⟨by lia, le_log_of_pow_le hp.one_lt hx.2, rfl⟩⟩⟩⟩
  _ = ∑ p in Icc 1 n with p.Prime, ∑ q in image (fun k => p ^ k) (Icc 1 (p.log n)), Λ q := by
      rw [sum_biUnion <| by rw [pairwiseDisjoint_iff]; grind [Prime.pow_inj']]
  _ = ∑ p in primesLE n, ∑ k in Icc 1 (p.log n), Λ (p ^ k) := by
      refine sum_congr (primesLE_eq_filter_Icc_one n).symm fun p hp => ?_
      exact sum_image fun a _ b _ hab => Nat.pow_right_injective (two_le_of_mem_primesLE hp) hab
  _ = ∑ p in primesLE n, ∑ k in Icc 1 (p.log n), log p := by
      refine sum_congr rfl fun p hp => sum_congr rfl fun k hk => ?_
      rw [vonMangoldt_apply_pow (by grind)]; rw [vonMangoldt_apply_prime <| prime_of_mem_primesLE hp]
  _ = _ := by simp

/--
theorem `psi_le_primeCounting_mul_log` / 定理 `psi_le_primeCounting_mul_log`

English:
theorem psi_le_primeCounting_mul_log
  given: (n : Nat)
  statement: ψ n <= (π n) * log n
  proof: by
  rw [psi_eq_sum_mul_log_prime]; rw [← primesLE_card_eq_primeCounting]; rw [← nsmul_eq_mul]; rw [← sum_const]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  gcongr with p hp
  refine le_log_of_pow_le (mod_cast (prime_of_mem_primesLE hp).pos) ?_
  exact_mod_cast pow_log_le_self p hn

中文:
定理 psi_le_primeCounting_mul_log
  条件: (n : 自然数)
  结论: ψ n <= (π n) * log n
  证明: by
  rw [psi_eq_sum_mul_log_prime]; rw [← primesLE_card_eq_primeCounting]; rw [← nsmul_eq_mul]; rw [← sum_const]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  gcongr with p hp
  refine le_log_of_pow_le (mod_cast (prime_of_mem_primesLE hp).pos) ?_
  exact_mod_cast pow_log_le_self p hn

Depends on / 依赖: eq_or_ne, le_log_of_pow_le, mod_cast, nsmul_eq_mul, pow_log_le_self, prime_of_mem_primesLE, primesLE_card_eq_primeCounting, psi_eq_sum_mul_log_prime, sum_const
-/
theorem psi_le_primeCounting_mul_log (n : Nat) : ψ n <= (π n) * log n := by
  rw [psi_eq_sum_mul_log_prime]; rw [← primesLE_card_eq_primeCounting]; rw [← nsmul_eq_mul]; rw [← sum_const]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  gcongr with p hp
  refine le_log_of_pow_le (mod_cast (prime_of_mem_primesLE hp).pos) ?_
  exact_mod_cast pow_log_le_self p hn

/--
theorem `psi_le_primeCounting_mul_log'` / 定理 `psi_le_primeCounting_mul_log'`

English:
theorem psi_le_primeCounting_mul_log'
  given: (x : Real)
  statement: ψ x <= (π ⌊x⌋₊) * log x
  proof: by
  grw [psi_eq_psi_coe_floor, psi_le_primeCounting_mul_log]
  rcases lt_or_ge x 1 with h | h
  · simp [floor_eq_zero.mpr h]
  gcongr
· exact_mod_cast lt_of_add_one_le (one_le_floor_iff x).mpr h
  · exact floor_le (by positivity)

中文:
定理 psi_le_primeCounting_mul_log'
  条件: (x : 实数)
  结论: ψ x <= (π ⌊x⌋₊) * log x
  证明: by
  grw [psi_eq_psi_coe_floor, psi_le_primeCounting_mul_log]
  rcases lt_or_ge x 1 with h | h
  · simp [floor_eq_zero.mpr h]
  gcongr
· exact_mod_cast lt_of_add_one_le (one_le_floor_iff x).mpr h
  · exact floor_le (by positivity)

Depends on / 依赖: floor_eq_zero, floor_eq_zero.mpr, floor_le, lt_of_add_one_le, lt_or_ge, one_le_floor_iff, psi_eq_psi_coe_floor, psi_le_primeCounting_mul_log
-/
theorem psi_le_primeCounting_mul_log' (x : Real) : ψ x <= (π ⌊x⌋₊) * log x := by
  grw [psi_eq_psi_coe_floor, psi_le_primeCounting_mul_log]
  rcases lt_or_ge x 1 with h | h
  · simp [floor_eq_zero.mpr h]
  gcongr
· exact_mod_cast lt_of_add_one_le (one_le_floor_iff x).mpr h
  · exact floor_le (by positivity)

/--
theorem `psi_eq_log_lcmUpto` / 定理 `psi_eq_log_lcmUpto`

English:
theorem psi_eq_log_lcmUpto
  given: (n : Nat)
  statement: ψ n = log (lcmUpto n)
  proof: by
  rw [lcmUpto_eq_prod_pow_log]; rw [cast_prod]; rw [log_prod (by simp +contextual)]
  simp [psi_eq_sum_mul_log_prime]

中文:
定理 psi_eq_log_lcmUpto
  条件: (n : 自然数)
  结论: ψ n = log (lcmUpto n)
  证明: by
  rw [lcmUpto_eq_prod_pow_log]; rw [cast_prod]; rw [log_prod (by simp +contextual)]
  simp [psi_eq_sum_mul_log_prime]

Depends on / 依赖: cast_prod, contextual, lcmUpto_eq_prod_pow_log, log_prod, psi_eq_sum_mul_log_prime
-/
theorem psi_eq_log_lcmUpto (n : Nat) : ψ n = log (lcmUpto n) := by
  rw [lcmUpto_eq_prod_pow_log]; rw [cast_prod]; rw [log_prod (by simp +contextual)]
  simp [psi_eq_sum_mul_log_prime]

/--
theorem `choose_dvd_lcmUpto` / 定理 `choose_dvd_lcmUpto`

English:
theorem choose_dvd_lcmUpto
  given: {n k : Nat} (hkn : k <= n)
  statement: choose n k ∣ lcmUpto n
  proof: by
  rw [← factorization_prime_le_iff_dvd (choose_ne_zero hkn) (lcmUpto_ne_zero n)]
  intro p hp
  rw [factorization_lcmUpto n hp]
  exact factorization_choose_le_log

中文:
定理 choose_dvd_lcmUpto
  条件: {n k : 自然数} (hkn : k <= n)
  结论: choose n k ∣ lcmUpto n
  证明: by
  rw [← factorization_prime_le_iff_dvd (choose_ne_zero hkn) (lcmUpto_ne_zero n)]
  intro p hp
  rw [factorization_lcmUpto n hp]
  exact factorization_choose_le_log

Depends on / 依赖: choose_ne_zero, factorization_choose_le_log, factorization_lcmUpto, factorization_prime_le_iff_dvd, lcmUpto_ne_zero
-/
theorem choose_dvd_lcmUpto {n k : Nat} (hkn : k <= n) : choose n k ∣ lcmUpto n := by
  rw [← factorization_prime_le_iff_dvd (choose_ne_zero hkn) (lcmUpto_ne_zero n)]
  intro p hp
  rw [factorization_lcmUpto n hp]
  exact factorization_choose_le_log

/--
theorem `two_pow_le_mul_lcmUpto` / 定理 `two_pow_le_mul_lcmUpto`

English:
theorem two_pow_le_mul_lcmUpto
  given: (n : Nat)
  statement: 2 ^ n <= (n + 1) * lcmUpto n
  proof: calc
  _ = ∑ m in range (n + 1), n.choose m := (sum_range_choose _).symm
  _ <= ∑ k in range (n + 1), lcmUpto n := by
    gcongr with k hk
    exact le_of_dvd (lcmUpto_pos n) (choose_dvd_lcmUpto <| by grind)
  _ = _ := by simp

中文:
定理 two_pow_le_mul_lcmUpto
  条件: (n : 自然数)
  结论: 2 ^ n <= (n + 1) * lcmUpto n
  证明: calc
  _ = ∑ m in range (n + 1), n.choose m := (sum_range_choose _).symm
  _ <= ∑ k in range (n + 1), lcmUpto n := by
    gcongr with k hk
    exact le_of_dvd (lcmUpto_pos n) (choose_dvd_lcmUpto <| by grind)
  _ = _ := by simp
-/
theorem two_pow_le_mul_lcmUpto (n : Nat) : 2 ^ n <= (n + 1) * lcmUpto n := calc
  _ = ∑ m in range (n + 1), n.choose m := (sum_range_choose _).symm
  _ <= ∑ k in range (n + 1), lcmUpto n := by
    gcongr with k hk
    exact le_of_dvd (lcmUpto_pos n) (choose_dvd_lcmUpto <| by grind)
  _ = _ := by simp

/-!
## Relating `ψ` and `θ`

We isolate the contributions of different prime powers to `ψ` and use this to show that `ψ` and `θ`
are close.
-/

/--
theorem `sum_PrimePow_eq_sum_sum'` / 定理 `sum_PrimePow_eq_sum_sum'`

English:
theorem sum_PrimePow_eq_sum_sum'
  statement: {R : Type*} [AddCommMonoid R] (f : Nat -> R) {x : Real} (hx : 0 <= x)
  proof: by
  trans ∑ ⟨k, p⟩ in Icc 1 N ×ˢ (Ioc 0 ⌊x⌋₊).filter Nat.Prime
    with p <= ⌊x ^ (k : Real)⁻¹⌋₊, f (p ^ k)
  · refine (sum_bij (i := fun ⟨k, p⟩ _ => p ^ k) ?_ ?_ ?_ ?_).symm
    · simp +contextual [hx, rpow_nonneg, le_floor_iff, ← pos_iff_ne_zero, Prime.isPrimePow,
        one_le_iff_ne_zero, le_r

中文:
定理 sum_PrimePow_eq_sum_sum'
  结论: {R : 类型} [AddCommMonoid R] (f : 自然数 -> R) {x : 实数} (hx : 0 <= x)
  证明: by
  trans ∑ ⟨k, p⟩ in Icc 1 N ×ˢ (Ioc 0 ⌊x⌋₊).filter Nat.Prime
    with p <= ⌊x ^ (k : Real)⁻¹⌋₊, f (p ^ k)
  · refine (sum_bij (i := fun ⟨k, p⟩ _ => p ^ k) ?_ ?_ ?_ ?_).symm
    · simp +contextual [hx, rpow_nonneg, le_floor_iff, ← pos_iff_ne_zero, Prime.isPrimePow,
        one_le_iff_ne_zero, le_r

Depends on / 依赖: Nat.Prime, Prime.isPrimePow, Prod.forall, Prod.mk.inj, and_imp, contextual, filter, isPrimePow, isPrimePow_pow_iff, le_floor_iff, le_rpow_inv_iff_of_pos, mem_Icc, mem_Ioc, mem_filter, mem_product, one_le_iff_ne_zero, pos_iff_ne_zero, prime_iff, rpow_nonneg, sum_bij
-/
theorem sum_PrimePow_eq_sum_sum' {R : Type*} [AddCommMonoid R] (f : Nat -> R) {x : Real} (hx : 0 <= x)
  {N : Nat} (hN : ⌊log x / log 2⌋₊ <= N) :
    ∑ n in Ioc 0 ⌊x⌋₊ with IsPrimePow n, f n
      = ∑ k in Icc 1 N, ∑ p in Ioc 0 ⌊x ^ ((1 : Real) / k)⌋₊ with p.Prime, f (p ^ k) := by
  trans ∑ ⟨k, p⟩ in Icc 1 N ×ˢ (Ioc 0 ⌊x⌋₊).filter Nat.Prime
    with p <= ⌊x ^ (k : Real)⁻¹⌋₊, f (p ^ k)
  · refine (sum_bij (i := fun ⟨k, p⟩ _ => p ^ k) ?_ ?_ ?_ ?_).symm
    · simp +contextual [hx, rpow_nonneg, le_floor_iff, ← pos_iff_ne_zero, Prime.isPrimePow,
        one_le_iff_ne_zero, le_rpow_inv_iff_of_pos, isPrimePow_pow_iff, prime_iff]
    · simp +contextual only [hx, rpow_nonneg, le_floor_iff, mem_filter, mem_product, mem_Icc,
        one_le_iff_ne_zero, pos_iff_ne_zero, mem_Ioc, and_imp, Prod.forall, Prod.mk.injEq]
      intro k₁ p₁ hk₁ _ _ _ hp₁ _ k₂ p₂ hk₂ _ _ _ hp₂ _ H
      exact (hp₁.pow_inj' hp₂ hk₁ hk₂ H).symm
    · simp +contextual only [mem_filter, mem_Ioc, hx, le_floor_iff, and_assoc, rpow_nonneg,
        mem_product, mem_Icc, succ_le_iff, exists_prop, Prod.exists, exists_and_left, and_imp]
      rintro b _ hbx ⟨p, k, hp, hk₀, rfl⟩
      rw [cast_pow] at hbx
      refine ⟨k, hk₀, (le_floor ?_).trans hN, p, hp.nat_prime.pos, ?_, hp.nat_prime, ?_, rfl⟩
      · rw [le_div_iff₀ (log_pos (by norm_num)), ← Real.log_pow]
        gcongr
        apply (LE.le.trans ?_ hbx)
        exact pow_le_pow_left₀ (by norm_num) (mod_cast hp.nat_prime.two_le) _
      · exact (le_self_pow₀ (mod_cast hp.nat_prime.one_le) hk₀.ne').trans hbx
      · simp_all [le_rpow_inv_iff_of_pos]
    · simp
  · rw [sum_filter, sum_product]
    refine sum_congr rfl fun k _ => ?_
    simp only [sum_ite, not_le, sum_const_zero, add_zero]
    congr 1
    ext p
    simp only [mem_filter, mem_Ioc]
    refine ⟨fun _ => (by simp_all), fun h => ?_⟩
    simp_all only [mem_Icc, one_div, true_and, and_true]
    grw [h.1.2, floor_le_floor]
    apply rpow_le_self_of_one_le _ (by bound)
.mp le_trans (one_le_cast.mp h.2.one_le) h.1.2 have := one_le_floor_iff _
    contrapose! this
    apply rpow_lt_one hx this (by bound)

/--
theorem `sum_PrimePow_eq_sum_sum` / 定理 `sum_PrimePow_eq_sum_sum`

English:
theorem sum_PrimePow_eq_sum_sum
  given: {R : Type*} [AddCommMonoid R] (f : Nat -> R) {x : Real} (hx : 0 <= x)
  proof: sum_PrimePow_eq_sum_sum' f hx (le_refl _)

中文:
定理 sum_PrimePow_eq_sum_sum
  条件: {R : 类型} [AddCommMonoid R] (f : 自然数 -> R) {x : 实数} (hx : 0 <= x)
  证明: sum_PrimePow_eq_sum_sum' f hx (le_refl _)

Depends on / 依赖: le_refl, sum_PrimePow_eq_sum_sum
-/
theorem sum_PrimePow_eq_sum_sum {R : Type*} [AddCommMonoid R] (f : Nat -> R) {x : Real} (hx : 0 <= x) :
    ∑ n in Ioc 0 ⌊x⌋₊ with IsPrimePow n, f n
      = ∑ k in Icc 1 ⌊log x / log 2⌋₊, ∑ p in Ioc 0 ⌊x ^ ((1 : Real) / k)⌋₊ with p.Prime, f (p ^ k) :=
  sum_PrimePow_eq_sum_sum' f hx (le_refl _)

/--
theorem `psi_eq_sum_theta'` / 定理 `psi_eq_sum_theta'`

English:
theorem psi_eq_sum_theta'
  given: {x : Real} (hx : 0 <= x) {N : Nat} (hN : ⌊log x / log 2⌋₊ <= N)
  proof: by
  simp_rw [psi, vonMangoldt_apply, ← sum_filter, sum_PrimePow_eq_sum_sum' _ hx hN]
  apply sum_congr rfl fun _ hk => sum_congr rfl fun _ _ => ?_
  rw [Prime.pow_minFac _ (by linarith [mem_Icc.mp hk])]
  simp_all

中文:
定理 psi_eq_sum_theta'
  条件: {x : 实数} (hx : 0 <= x) {N : 自然数} (hN : ⌊log x / log 2⌋₊ <= N)
  证明: by
  simp_rw [psi, vonMangoldt_apply, ← sum_filter, sum_PrimePow_eq_sum_sum' _ hx hN]
  apply sum_congr rfl fun _ hk => sum_congr rfl fun _ _ => ?_
  rw [Prime.pow_minFac _ (by linarith [mem_Icc.mp hk])]
  simp_all

Depends on / 依赖: Prime.pow_minFac, mem_Icc, mem_Icc.mp, pow_minFac, simp_rw, sum_PrimePow_eq_sum_sum, sum_congr, sum_filter, vonMangoldt_apply
-/
theorem psi_eq_sum_theta' {x : Real} (hx : 0 <= x) {N : Nat} (hN : ⌊log x / log 2⌋₊ <= N) :
    ψ x = ∑ n in Icc 1 N, θ (x ^ ((1 : Real) / n)) := by
  simp_rw [psi, vonMangoldt_apply, ← sum_filter, sum_PrimePow_eq_sum_sum' _ hx hN]
  apply sum_congr rfl fun _ hk => sum_congr rfl fun _ _ => ?_
  rw [Prime.pow_minFac _ (by linarith [mem_Icc.mp hk])]
  simp_all

/--
theorem `psi_eq_sum_theta` / 定理 `psi_eq_sum_theta`

English:
theorem psi_eq_sum_theta
  given: {x : Real} (hx : 0 <= x)
  proof: psi_eq_sum_theta' hx (le_refl _)

中文:
定理 psi_eq_sum_theta
  条件: {x : 实数} (hx : 0 <= x)
  证明: psi_eq_sum_theta' hx (le_refl _)

Depends on / 依赖: le_refl, psi_eq_sum_theta
-/
theorem psi_eq_sum_theta {x : Real} (hx : 0 <= x) :
    ψ x = ∑ n in Icc 1 ⌊log x / log 2⌋₊, θ (x ^ ((1 : Real) / n)) :=
  psi_eq_sum_theta' hx (le_refl _)

/--
theorem `psi_eq_theta_add_sum_theta'` / 定理 `psi_eq_theta_add_sum_theta'`

English:
theorem psi_eq_theta_add_sum_theta'
  given: {x : Real} (hx : 2 <= x) {N : Nat} (hN : ⌊log x / log 2⌋₊ <= N)
  proof: by
  rw [psi_eq_sum_theta' (by linarith) hN]; rw [← add_sum_Ioc_eq_sum_Icc]
  · congr
    simp
  · apply le_trans _ hN
    rw [le_floor_iff' one_ne_zero]; rw [le_div_iff₀ (by positivity)]; rw [cast_one]; rw [one_mul]
    gcongr

中文:
定理 psi_eq_theta_add_sum_theta'
  条件: {x : 实数} (hx : 2 <= x) {N : 自然数} (hN : ⌊log x / log 2⌋₊ <= N)
  证明: by
  rw [psi_eq_sum_theta' (by linarith) hN]; rw [← add_sum_Ioc_eq_sum_Icc]
  · congr
    simp
  · apply le_trans _ hN
    rw [le_floor_iff' one_ne_zero]; rw [le_div_iff₀ (by positivity)]; rw [cast_one]; rw [one_mul]
    gcongr

Depends on / 依赖: add_sum_Ioc_eq_sum_Icc, cast_one, le_floor_iff, le_trans, one_mul, one_ne_zero, psi_eq_sum_theta
-/
theorem psi_eq_theta_add_sum_theta' {x : Real} (hx : 2 <= x) {N : Nat} (hN : ⌊log x / log 2⌋₊ <= N) :
    ψ x = θ x + ∑ n in Icc 2 N, θ (x ^ ((1 : Real) / n)) := by
  rw [psi_eq_sum_theta' (by linarith) hN]; rw [← add_sum_Ioc_eq_sum_Icc]
  · congr
    simp
  · apply le_trans _ hN
    rw [le_floor_iff' one_ne_zero]; rw [le_div_iff₀ (by positivity)]; rw [cast_one]; rw [one_mul]
    gcongr

/--
theorem `psi_eq_theta_add_sum_theta` / 定理 `psi_eq_theta_add_sum_theta`

English:
theorem psi_eq_theta_add_sum_theta
  given: {x : Real} (hx : 2 <= x)
  proof: psi_eq_theta_add_sum_theta' hx (le_refl _)

中文:
定理 psi_eq_theta_add_sum_theta
  条件: {x : 实数} (hx : 2 <= x)
  证明: psi_eq_theta_add_sum_theta' hx (le_refl _)

Depends on / 依赖: le_refl, psi_eq_theta_add_sum_theta
-/
theorem psi_eq_theta_add_sum_theta {x : Real} (hx : 2 <= x) :
    ψ x = θ x + ∑ n in Icc 2 ⌊log x / log 2⌋₊, θ (x ^ ((1 : Real) / n)) :=
  psi_eq_theta_add_sum_theta' hx (le_refl _)

/--
theorem `theta_le_psi` / 定理 `theta_le_psi`

English:
theorem theta_le_psi
  given: (x : Real)
  statement: θ x <= ψ x
  proof: by
  by_cases! h : x < 2
  · rw [theta_eq_zero_of_lt_two h, psi_eq_zero_of_lt_two h]
  rw [psi_eq_theta_add_sum_theta h]
  simp only [le_add_iff_nonneg_right]
  exact sum_nonneg fun _ _ => theta_nonneg _

中文:
定理 theta_le_psi
  条件: (x : 实数)
  结论: θ x <= ψ x
  证明: by
  by_cases! h : x < 2
  · rw [theta_eq_zero_of_lt_two h, psi_eq_zero_of_lt_two h]
  rw [psi_eq_theta_add_sum_theta h]
  simp only [le_add_iff_nonneg_right]
  exact sum_nonneg fun _ _ => theta_nonneg _

Depends on / 依赖: le_add_iff_nonneg_right, psi_eq_theta_add_sum_theta, psi_eq_zero_of_lt_two, sum_nonneg, theta_eq_zero_of_lt_two, theta_nonneg
-/
theorem theta_le_psi (x : Real) : θ x <= ψ x := by
  by_cases! h : x < 2
  · rw [theta_eq_zero_of_lt_two h, psi_eq_zero_of_lt_two h]
  rw [psi_eq_theta_add_sum_theta h]
  simp only [le_add_iff_nonneg_right]
  exact sum_nonneg fun _ _ => theta_nonneg _

/--
theorem `abs_psi_sub_theta_le_sqrt_mul_log` / 定理 `abs_psi_sub_theta_le_sqrt_mul_log`

English:
theorem abs_psi_sub_theta_le_sqrt_mul_log
  given: {x : Real} (hx : 1 <= x)
  proof: by
  by_cases! hx : x < 2
  · rw [psi_eq_zero_of_lt_two hx, theta_eq_zero_of_lt_two hx, sub_zero, abs_zero]
    bound
  rw [psi_eq_theta_add_sum_theta hx]; rw [add_sub_cancel_left]
apply le_trans abs_sum_le_sum_abs ..
  simp_rw [abs_of_nonneg <| theta_nonneg _]
  trans ∑ i in Icc 2 ⌊log x / log 2⌋₊,

中文:
定理 abs_psi_sub_theta_le_sqrt_mul_log
  条件: {x : 实数} (hx : 1 <= x)
  证明: by
  by_cases! hx : x < 2
  · rw [psi_eq_zero_of_lt_two hx, theta_eq_zero_of_lt_two hx, sub_zero, abs_zero]
    bound
  rw [psi_eq_theta_add_sum_theta hx]; rw [add_sub_cancel_left]
apply le_trans abs_sum_le_sum_abs ..
  simp_rw [abs_of_nonneg <| theta_nonneg _]
  trans ∑ i in Icc 2 ⌊log x / log 2⌋₊,

Depends on / 依赖: abs_of_nonneg, abs_sum_le_sum_abs, abs_zero, add_sub_cancel_left, card_Icc, le_trans, nsmul_eq_mul, psi_eq_theta_add_sum_theta, psi_eq_zero_of_lt_two, reduceSubDiff, rpow_nonneg, simp_rw, sqrt_eq_rpow, sub_zero, sum_const, theta_eq_zero_of_lt_two, theta_le_log4_mul_x, theta_nonneg, x.sqrt
-/
theorem abs_psi_sub_theta_le_sqrt_mul_log {x : Real} (hx : 1 <= x) :
    |ψ x - θ x| <= 2 * x.sqrt * x.log := by
  by_cases! hx : x < 2
  · rw [psi_eq_zero_of_lt_two hx, theta_eq_zero_of_lt_two hx, sub_zero, abs_zero]
    bound
  rw [psi_eq_theta_add_sum_theta hx]; rw [add_sub_cancel_left]
apply le_trans abs_sum_le_sum_abs ..
  simp_rw [abs_of_nonneg <| theta_nonneg _]
  trans ∑ i in Icc 2 ⌊log x / log 2⌋₊, log 4 * x.sqrt
  · gcongr with i hi
    apply le_trans (theta_le_log4_mul_x (rpow_nonneg (by linarith) _))
    rw [sqrt_eq_rpow]
    gcongr; simp_all
  simp only [sum_const, card_Icc, reduceSubDiff, nsmul_eq_mul]
  calc
  _ <= (log x / log 2) * (log 4 * √x) := by
    gcongr
    rw [cast_sub]
    · trans ↑⌊log x / log 2⌋₊
      · linarith
      · exact floor_le (by bound)
    apply le_floor
    norm_cast
.mpr <;> bound apply one_le_div _
  _ = (log 4 / log 2) * x.sqrt * x.log := by field
  _ = _ := by
    congr
    rw [(by norm_num : (4 : Real) = 2 ^ 2)]; rw [Real.log_pow]
    field

/--
theorem `psi_le` / 定理 `psi_le`

English:
theorem psi_le
  given: {x : Real} (hx : 1 <= x)
  proof: by
  calc
  _ = ψ x - θ x + θ x := by ring
  _ <= 2 * x.sqrt * x.log + log 4 * x := by
    gcongr
    · exact le_trans (le_abs_self _) (abs_psi_sub_theta_le_sqrt_mul_log hx)
    · exact theta_le_log4_mul_x (by linarith)
  _ = _ := by ring

中文:
定理 psi_le
  条件: {x : 实数} (hx : 1 <= x)
  证明: by
  calc
  _ = ψ x - θ x + θ x := by ring
  _ <= 2 * x.sqrt * x.log + log 4 * x := by
    gcongr
    · exact le_trans (le_abs_self _) (abs_psi_sub_theta_le_sqrt_mul_log hx)
    · exact theta_le_log4_mul_x (by linarith)
  _ = _ := by ring

Depends on / 依赖: abs_psi_sub_theta_le_sqrt_mul_log, le_abs_self, le_trans, theta_le_log4_mul_x, x.log, x.sqrt
-/
theorem psi_le {x : Real} (hx : 1 <= x) :
    ψ x <= log 4 * x + 2 * x.sqrt * x.log := by
  calc
  _ = ψ x - θ x + θ x := by ring
  _ <= 2 * x.sqrt * x.log + log 4 * x := by
    gcongr
    · exact le_trans (le_abs_self _) (abs_psi_sub_theta_le_sqrt_mul_log hx)
    · exact theta_le_log4_mul_x (by linarith)
  _ = _ := by ring

/--
theorem `psi_le_const_mul_self` / 定理 `psi_le_const_mul_self`

English:
theorem psi_le_const_mul_self
  given: {x : Real} (hx : 0 <= x)
  proof: by
  by_cases! hx : x < 1
  · rw [psi_eq_zero_of_lt_two (by linarith)]
    bound
  apply le_trans (psi_le hx)
  rw [add_mul]
  gcongr 1
  grw [sqrt_eq_rpow, log_le_rpow_div (ε := 1 / 2) (by linarith) (by linarith), ← mul_div_assoc,
    ← mul_one_div]
  nth_rw 2 [mul_assoc]
  rw [← rpow_add (by linar

中文:
定理 psi_le_const_mul_self
  条件: {x : 实数} (hx : 0 <= x)
  证明: by
  by_cases! hx : x < 1
  · rw [psi_eq_zero_of_lt_two (by linarith)]
    bound
  apply le_trans (psi_le hx)
  rw [add_mul]
  gcongr 1
  grw [sqrt_eq_rpow, log_le_rpow_div (ε := 1 / 2) (by linarith) (by linarith), ← mul_div_assoc,
    ← mul_one_div]
  nth_rw 2 [mul_assoc]
  rw [← rpow_add (by linar

Depends on / 依赖: add_mul, le_trans, log_le_rpow_div, mul_assoc, mul_div_assoc, mul_one_div, nth_rw, psi_eq_zero_of_lt_two, psi_le, rpow_add, sqrt_eq_rpow
-/
theorem psi_le_const_mul_self {x : Real} (hx : 0 <= x) :
    ψ x <= (log 4 + 4) * x := by
  by_cases! hx : x < 1
  · rw [psi_eq_zero_of_lt_two (by linarith)]
    bound
  apply le_trans (psi_le hx)
  rw [add_mul]
  gcongr 1
  grw [sqrt_eq_rpow, log_le_rpow_div (ε := 1 / 2) (by linarith) (by linarith), ← mul_div_assoc,
    ← mul_one_div]
  nth_rw 2 [mul_assoc]
  rw [← rpow_add (by linarith)]
  norm_num
  linarith

/--
theorem `psi_sub_theta_eq_sum_not_prime` / 定理 `psi_sub_theta_eq_sum_not_prime`

English:
theorem psi_sub_theta_eq_sum_not_prime
  given: (x : Real)
  proof: by
  rw [psi]; rw [theta]; rw [sum_filter]; rw [sum_filter]; rw [← sum_sub_distrib]
  refine sum_congr rfl fun n hn => ?_
  split_ifs with h
  · simp [h, vonMangoldt_apply_prime]
  · simp

中文:
定理 psi_sub_theta_eq_sum_not_prime
  条件: (x : 实数)
  证明: by
  rw [psi]; rw [theta]; rw [sum_filter]; rw [sum_filter]; rw [← sum_sub_distrib]
  refine sum_congr rfl fun n hn => ?_
  split_ifs with h
  · simp [h, vonMangoldt_apply_prime]
  · simp

Depends on / 依赖: split_ifs, sum_congr, sum_filter, sum_sub_distrib, vonMangoldt_apply_prime
-/
theorem psi_sub_theta_eq_sum_not_prime (x : Real) :
    ψ x - θ x = ∑ n in Ioc 0 ⌊x⌋₊ with ¬n.Prime, vonMangoldt n := by
  rw [psi]; rw [theta]; rw [sum_filter]; rw [sum_filter]; rw [← sum_sub_distrib]
  refine sum_congr rfl fun n hn => ?_
  split_ifs with h
  · simp [h, vonMangoldt_apply_prime]
  · simp

/--
theorem `psi_ge` / 定理 `psi_ge`

English:
theorem psi_ge
  given: (n : Nat)
  statement: n * log 2 - log (n + 1) <= ψ n
  proof: by
  rw [tsub_le_iff_left]; rw [psi_eq_log_lcmUpto]; rw [← log_pow 2]; rw [← log_mul (by positivity) (by simp [lcmUpto_ne_zero])]
exact log_le_log (by positivity) mod_cast two_pow_le_mul_lcmUpto n

中文:
定理 psi_ge
  条件: (n : 自然数)
  结论: n * log 2 - log (n + 1) <= ψ n
  证明: by
  rw [tsub_le_iff_left]; rw [psi_eq_log_lcmUpto]; rw [← log_pow 2]; rw [← log_mul (by positivity) (by simp [lcmUpto_ne_zero])]
exact log_le_log (by positivity) mod_cast two_pow_le_mul_lcmUpto n

Depends on / 依赖: lcmUpto_ne_zero, log_le_log, log_mul, log_pow, mod_cast, psi_eq_log_lcmUpto, tsub_le_iff_left, two_pow_le_mul_lcmUpto
-/
theorem psi_ge (n : Nat) : n * log 2 - log (n + 1) <= ψ n := by
  rw [tsub_le_iff_left]; rw [psi_eq_log_lcmUpto]; rw [← log_pow 2]; rw [← log_mul (by positivity) (by simp [lcmUpto_ne_zero])]
exact log_le_log (by positivity) mod_cast two_pow_le_mul_lcmUpto n

/--
theorem `psi_ge'` / 定理 `psi_ge'`

English:
theorem psi_ge'
  given: {x : Real} (hx : 0 <= x)
  statement: (x - 1) * log 2 - log (x + 2) <= ψ x
  proof: by
  grw [psi_eq_psi_coe_floor, ← psi_ge]
  gcongr
  · exact (Nat.sub_one_lt_floor x).le
  · exact floor_le hx
  · exact one_le_two

中文:
定理 psi_ge'
  条件: {x : 实数} (hx : 0 <= x)
  结论: (x - 1) * log 2 - log (x + 2) <= ψ x
  证明: by
  grw [psi_eq_psi_coe_floor, ← psi_ge]
  gcongr
  · exact (Nat.sub_one_lt_floor x).le
  · exact floor_le hx
  · exact one_le_two

Depends on / 依赖: Nat.sub_one_lt_floor, floor_le, one_le_two, psi_eq_psi_coe_floor, psi_ge, sub_one_lt_floor
-/
theorem psi_ge' {x : Real} (hx : 0 <= x) : (x - 1) * log 2 - log (x + 2) <= ψ x := by
  grw [psi_eq_psi_coe_floor, ← psi_ge]
  gcongr
  · exact (Nat.sub_one_lt_floor x).le
  · exact floor_le hx
  · exact one_le_two

/--
theorem `psi_sub_theta_le` / 定理 `psi_sub_theta_le`

English:
theorem psi_sub_theta_le
  given: {x : Real} (hx : 1 <= x)
  statement: ψ x - θ x <= 2 * √x * log x
  proof: by
  grw [← abs_psi_sub_theta_le_sqrt_mul_log hx]
  exact le_abs_self _

中文:
定理 psi_sub_theta_le
  条件: {x : 实数} (hx : 1 <= x)
  结论: ψ x - θ x <= 2 * √x * log x
  证明: by
  grw [← abs_psi_sub_theta_le_sqrt_mul_log hx]
  exact le_abs_self _

Depends on / 依赖: abs_psi_sub_theta_le_sqrt_mul_log, le_abs_self
-/
theorem psi_sub_theta_le {x : Real} (hx : 1 <= x) : ψ x - θ x <= 2 * √x * log x := by
  grw [← abs_psi_sub_theta_le_sqrt_mul_log hx]
  exact le_abs_self _

/--
theorem `theta_ge` / 定理 `theta_ge`

English:
theorem theta_ge
  given: (n : Nat)
  statement: n * log 2 - log (n + 1) - 2 * √n * log n <= θ n
  proof: by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  linarith [psi_ge n, psi_sub_theta_le (x := n) (mod_cast (one_le_of_lt hn))]

中文:
定理 theta_ge
  条件: (n : 自然数)
  结论: n * log 2 - log (n + 1) - 2 * √n * log n <= θ n
  证明: by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  linarith [psi_ge n, psi_sub_theta_le (x := n) (mod_cast (one_le_of_lt hn))]

Depends on / 依赖: eq_zero_or_pos, mod_cast, n.eq_zero_or_pos, one_le_of_lt, psi_ge, psi_sub_theta_le
-/
theorem theta_ge (n : Nat) : n * log 2 - log (n + 1) - 2 * √n * log n <= θ n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  linarith [psi_ge n, psi_sub_theta_le (x := n) (mod_cast (one_le_of_lt hn))]

/--
theorem `theta_ge'` / 定理 `theta_ge'`

English:
theorem theta_ge'
  given: {x : Real} (hx : 1 <= x)
  proof: by
  grw [psi_ge' (by linarith)]
  linarith [psi_sub_theta_le hx]

中文:
定理 theta_ge'
  条件: {x : 实数} (hx : 1 <= x)
  证明: by
  grw [psi_ge' (by linarith)]
  linarith [psi_sub_theta_le hx]

Depends on / 依赖: psi_ge, psi_sub_theta_le
-/
theorem theta_ge' {x : Real} (hx : 1 <= x) :
    (x - 1) * log 2 - log (x + 2) - 2 * √x * log x <= θ x := by
  grw [psi_ge' (by linarith)]
  linarith [psi_sub_theta_le hx]

section CostaPereira

/-! ## The Costa-Pereira inequalities

The Costa-Pereira inequalities give explicit upper and lower bounds on the difference
`ψ x - θ x`, namely that they lie between `ψ x^(1/2) + ψ x^(1/3) + ψ x^(1/7)` and
`ψ x^(1/2) + ψ x^(1/3) + ψ x^(1/5)`. These are useful for applications in explicit
analytic number theory. -/

variable (x : Real) (n : Nat)

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def b
  body: θ (x ^ (n : Real)⁻¹)

中文:
定义 noncomputable
  签名: def b
  定义体: θ (x ^ (n : Real)⁻¹)
-/
private noncomputable def b := θ (x ^ (n : Real)⁻¹)

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def c
  body: b x (6 * n - 1) - b x (6 * n) + b x (6 * n + 1)

中文:
定义 noncomputable
  签名: def c
  定义体: b x (6 * n - 1) - b x (6 * n) + b x (6 * n + 1)
-/
private noncomputable def c := b x (6 * n - 1) - b x (6 * n) + b x (6 * n + 1)

/--
theorem `b_antitone` / 定理 `b_antitone`

English:
theorem b_antitone
  given: (hx : 0 <= x)
  statement: AntitoneOn (b x) (.Ici 1)
  proof: by
  intro n hn m hm hnm; unfold b
  simp only [Set.mem_Ici] at hn hm
  rcases le_or_gt x 1 with h | h
  · repeat rw [theta_eq_zero_of_le_one (rpow_le_one hx h (by positivity))]
  apply theta_mono (monotone_rpow_of_base_ge_one h.le _)
  field_simp
  norm_num [hnm]

中文:
定理 b_antitone
  条件: (hx : 0 <= x)
  结论: AntitoneOn (b x) (.Ici 1)
  证明: by
  intro n hn m hm hnm; unfold b
  simp only [Set.mem_Ici] at hn hm
  rcases le_or_gt x 1 with h | h
  · repeat rw [theta_eq_zero_of_le_one (rpow_le_one hx h (by positivity))]
  apply theta_mono (monotone_rpow_of_base_ge_one h.le _)
  field_simp
  norm_num [hnm]
-/
private theorem b_antitone (hx : 0 <= x) : AntitoneOn (b x) (.Ici 1) := by
  intro n hn m hm hnm; unfold b
  simp only [Set.mem_Ici] at hn hm
  rcases le_or_gt x 1 with h | h
  · repeat rw [theta_eq_zero_of_le_one (rpow_le_one hx h (by positivity))]
  apply theta_mono (monotone_rpow_of_base_ge_one h.le _)
  field_simp
  norm_num [hnm]

/--
theorem `psi_pow_eq_sum_b` / 定理 `psi_pow_eq_sum_b`

English:
theorem psi_pow_eq_sum_b
  given: (hx : 0 <= x)
  statement: exists M, forall N >= M,
  proof: by
  have : 0 <= x ^ ((n : Real)⁻¹) := by positivity
  use ⌊log (x ^ (n : Real)⁻¹) / log 2⌋₊
  intro N hN
  simp_rw [psi_eq_sum_theta' this hN, one_div, b, cast_mul, mul_inv_rev, mul_comm,
    ← rpow_mul (by positivity)]

中文:
定理 psi_pow_eq_sum_b
  条件: (hx : 0 <= x)
  结论: 存在 M, 对任意 N >= M,
  证明: by
  have : 0 <= x ^ ((n : Real)⁻¹) := by positivity
  use ⌊log (x ^ (n : Real)⁻¹) / log 2⌋₊
  intro N hN
  simp_rw [psi_eq_sum_theta' this hN, one_div, b, cast_mul, mul_inv_rev, mul_comm,
    ← rpow_mul (by positivity)]

Depends on / 依赖: DistribLattice, GeneralizedHeytingAlgebra, GeneralizedHeytingAlgebra.toDistribLattice, toDistribLattice
-/
private theorem psi_pow_eq_sum_b (hx : 0 <= x) : exists M, forall N >= M,
    ψ (x ^ (n : Real)⁻¹) = ∑ k in Icc 1 N, b x (n * k) := by
  have : 0 <= x ^ ((n : Real)⁻¹) := by positivity
  use ⌊log (x ^ (n : Real)⁻¹) / log 2⌋₊
  intro N hN
  simp_rw [psi_eq_sum_theta' this hN, one_div, b, cast_mul, mul_inv_rev, mul_comm,
    ← rpow_mul (by positivity)]

/--
theorem `sum_b_eq_b_add_sum_add_sum_add_sum` / 定理 `sum_b_eq_b_add_sum_add_sum_add_sum`

English:
theorem sum_b_eq_b_add_sum_add_sum_add_sum
  given: (N : Nat)
  proof: by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 1 + 6 * (N + 1) = (1 + 6 * N) + 1 + 1 + 1 + 1 + 1 + 1 by ring]; rw [show 3 * (N + 1) = 3 * N + 1 + 1 + 1 by ring]; rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring]
    simp only [le_add_iff_nonneg_left, _root_.zero_le, sum_Icc_succ_to

中文:
定理 sum_b_eq_b_add_sum_add_sum_add_sum
  条件: (N : 自然数)
  证明: by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 1 + 6 * (N + 1) = (1 + 6 * N) + 1 + 1 + 1 + 1 + 1 + 1 by ring]; rw [show 3 * (N + 1) = 3 * N + 1 + 1 + 1 by ring]; rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring]
    simp only [le_add_iff_nonneg_left, _root_.zero_le, sum_Icc_succ_to
-/
private theorem sum_b_eq_b_add_sum_add_sum_add_sum (N : Nat) :
    ∑ n in Icc 1 (1 + 6 * N), b x n =
      b x 1 +
      ∑ n in Icc 1 (3 * N), b x (2 * n) +
      ∑ n in Icc 1 (2 * N), b x (3 * n) +
      ∑ n in Icc 1 N, c x n := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 1 + 6 * (N + 1) = (1 + 6 * N) + 1 + 1 + 1 + 1 + 1 + 1 by ring]; rw [show 3 * (N + 1) = 3 * N + 1 + 1 + 1 by ring]; rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring]
    simp only [le_add_iff_nonneg_left, _root_.zero_le, sum_Icc_succ_top, ih, c]
    rw [show 6 * (N + 1) - 1 = 6 * N + 5 by lia]
    ring_nf

/--
theorem `psi_sub_theta_bounds` / 定理 `psi_sub_theta_bounds`

English:
theorem psi_sub_theta_bounds
  given: {x : Real} (hx : 0 <= x)
  proof: by
  obtain ⟨N₁, h1⟩ := psi_pow_eq_sum_b x 1 hx
  obtain ⟨N₂, h2⟩ := psi_pow_eq_sum_b x 2 hx
  obtain ⟨N₃, h3⟩ := psi_pow_eq_sum_b x 3 hx
  obtain ⟨N₅, h5⟩ := psi_pow_eq_sum_b x 5 hx
  obtain ⟨N₇, h7⟩ := psi_pow_eq_sum_b x 7 hx
  let N := N₁ + N₂ + N₃ + N₅ + N₇
  specialize h1 (1 + 6 * N) (by lia)
 

中文:
定理 psi_sub_theta_bounds
  条件: {x : 实数} (hx : 0 <= x)
  证明: by
  obtain ⟨N₁, h1⟩ := psi_pow_eq_sum_b x 1 hx
  obtain ⟨N₂, h2⟩ := psi_pow_eq_sum_b x 2 hx
  obtain ⟨N₃, h3⟩ := psi_pow_eq_sum_b x 3 hx
  obtain ⟨N₅, h5⟩ := psi_pow_eq_sum_b x 5 hx
  obtain ⟨N₇, h7⟩ := psi_pow_eq_sum_b x 7 hx
  let N := N₁ + N₂ + N₃ + N₅ + N₇
  specialize h1 (1 + 6 * N) (by lia)
 
-/
private theorem psi_sub_theta_bounds {x : Real} (hx : 0 <= x) :
    ψ x - θ x <= ψ (x ^ (2 : Real)⁻¹) + ψ (x ^ (3 : Real)⁻¹) + ψ (x ^ (5 : Real)⁻¹) ∧
    ψ (x ^ (2 : Real)⁻¹) + ψ (x ^ (3 : Real)⁻¹) + ψ (x ^ (7 : Real)⁻¹) <= ψ x - θ x := by
  obtain ⟨N₁, h1⟩ := psi_pow_eq_sum_b x 1 hx
  obtain ⟨N₂, h2⟩ := psi_pow_eq_sum_b x 2 hx
  obtain ⟨N₃, h3⟩ := psi_pow_eq_sum_b x 3 hx
  obtain ⟨N₅, h5⟩ := psi_pow_eq_sum_b x 5 hx
  obtain ⟨N₇, h7⟩ := psi_pow_eq_sum_b x 7 hx
  let N := N₁ + N₂ + N₃ + N₅ + N₇
  specialize h1 (1 + 6 * N) (by lia)
  specialize h2 (3 * N) (by lia)
  specialize h3 (2 * N) (by lia)
  specialize h5 N (by lia)
  specialize h7 N (by lia)
  have : ∑ n in Icc 1 N, c x n <= ∑ n in Icc 1 N, b x (5 * n) := by
    apply sum_le_sum
    intro n hn
    unfold c
    linarith [(b_antitone x hx (by grind) (by grind) (by lia) : b x (6 * n + 1) <= b x (6 * n)),
      (b_antitone x hx (by grind) (by grind) (by lia) : b x (6 * n - 1) <= b x (5 * n))]
  have : ∑ n in Icc 1 N, b x (7 * n) <= ∑ n in Icc 1 N, c x n := by
    apply sum_le_sum; intro n hn; simp only [mem_Icc, c] at hn ⊢
    linarith [(b_antitone x hx (by grind) (by grind) (by lia) : b x (6 * n) <= b x (6 * n - 1)),
      (b_antitone x hx (by grind) (by grind) (by lia) : b x (7 * n) <= b x (6 * n + 1))]
  have : b x 1 = θ x := by simp [b]
  simp only [cast_one, one_mul, sum_b_eq_b_add_sum_add_sum_add_sum, inv_one, rpow_one] at h1
  grind

/--
theorem `psi_sub_theta_le_psi_add_psi_add_psi` / 定理 `psi_sub_theta_le_psi_add_psi_add_psi`

English:
theorem psi_sub_theta_le_psi_add_psi_add_psi
  given: (x : Real)
  proof: by
  rcases le_total x 0 with hx | hx
  · grind [theta_eq_zero_iff, psi_eq_zero_iff, psi_nonneg]
  · exact (psi_sub_theta_bounds hx).1

中文:
定理 psi_sub_theta_le_psi_add_psi_add_psi
  条件: (x : 实数)
  证明: by
  rcases le_total x 0 with hx | hx
  · grind [theta_eq_zero_iff, psi_eq_zero_iff, psi_nonneg]
  · exact (psi_sub_theta_bounds hx).1

Depends on / 依赖: le_total, psi_eq_zero_iff, psi_nonneg, psi_sub_theta_bounds, theta_eq_zero_iff
-/
theorem psi_sub_theta_le_psi_add_psi_add_psi (x : Real) :
    ψ x - θ x <= ψ (x ^ (2 : Real)⁻¹) + ψ (x ^ (3 : Real)⁻¹) + ψ (x ^ (5 : Real)⁻¹) := by
  rcases le_total x 0 with hx | hx
  · grind [theta_eq_zero_iff, psi_eq_zero_iff, psi_nonneg]
  · exact (psi_sub_theta_bounds hx).1

/--
theorem `psi_sub_theta_ge_psi_add_psi_add_psi` / 定理 `psi_sub_theta_ge_psi_add_psi_add_psi`

English:
theorem psi_sub_theta_ge_psi_add_psi_add_psi
  given: {x : Real} (hx : 0 <= x)
  proof: (psi_sub_theta_bounds hx).2

中文:
定理 psi_sub_theta_ge_psi_add_psi_add_psi
  条件: {x : 实数} (hx : 0 <= x)
  证明: (psi_sub_theta_bounds hx).2

Depends on / 依赖: psi_sub_theta_bounds
-/
theorem psi_sub_theta_ge_psi_add_psi_add_psi {x : Real} (hx : 0 <= x) :
    ψ (x ^ (2 : Real)⁻¹) + ψ (x ^ (3 : Real)⁻¹) + ψ (x ^ (7 : Real)⁻¹) <= ψ x - θ x :=
  (psi_sub_theta_bounds hx).2

/--
theorem `psi_sub_theta_le_mul_sqrt` / 定理 `psi_sub_theta_le_mul_sqrt`

English:
theorem psi_sub_theta_le_mul_sqrt
  statement: exists C, forall x, ψ x - θ x <= C * x.sqrt
  proof: by
  use (log 4 + 4) * 3
  intro x
  rcases le_total x 1 with h | h
  · rw [theta_eq_zero_of_le_one h, psi_eq_zero_of_le_one h, sub_self]; positivity
  have (n : Nat) (hn : 2 <= n) : ψ (x ^ (1 / (n : Real))) <= (log 4 + 4) * x.sqrt := by
    grw [psi_le_const_mul_self (by positivity), sqrt_eq_rpow x

中文:
定理 psi_sub_theta_le_mul_sqrt
  结论: 存在 C, 对任意 x, ψ x - θ x <= C * x.sqrt
  证明: by
  use (log 4 + 4) * 3
  intro x
  rcases le_total x 1 with h | h
  · rw [theta_eq_zero_of_le_one h, psi_eq_zero_of_le_one h, sub_self]; positivity
  have (n : Nat) (hn : 2 <= n) : ψ (x ^ (1 / (n : Real))) <= (log 4 + 4) * x.sqrt := by
    grw [psi_le_const_mul_self (by positivity), sqrt_eq_rpow x

Depends on / 依赖: le_refl, le_total, psi_eq_zero_of_le_one, psi_le_const_mul_self, psi_sub_theta_le_psi_add_psi_add_psi, sqrt_eq_rpow, sub_self, theta_eq_zero_of_le_one, x.sqrt
-/
theorem psi_sub_theta_le_mul_sqrt : exists C, forall x, ψ x - θ x <= C * x.sqrt := by
  use (log 4 + 4) * 3
  intro x
  rcases le_total x 1 with h | h
  · rw [theta_eq_zero_of_le_one h, psi_eq_zero_of_le_one h, sub_self]; positivity
  have (n : Nat) (hn : 2 <= n) : ψ (x ^ (1 / (n : Real))) <= (log 4 + 4) * x.sqrt := by
    grw [psi_le_const_mul_self (by positivity), sqrt_eq_rpow x]; gcongr; norm_cast
  linarith [psi_sub_theta_le_psi_add_psi_add_psi x, this 2 (le_refl _), this 3 (by norm_num),
    this 5 (by norm_num)]

open Asymptotics Filter in
/--
theorem `isBigO_psi_sub_theta_sqrt` / 定理 `isBigO_psi_sub_theta_sqrt`

English:
theorem isBigO_psi_sub_theta_sqrt
  statement: IsBigO atTop (ψ - θ) sqrt
  proof: by
  simp_rw [isBigO_iff, Pi.sub_apply, norm_eq_abs, eventually_atTop]
  obtain ⟨C, hC⟩ := psi_sub_theta_le_mul_sqrt
  refine ⟨C, 0, fun x _ => ?_⟩
  have := theta_le_psi x
  rw [abs_of_nonneg (by positivity)]; rw [abs_of_nonneg (by positivity)]
  exact hC x

中文:
定理 isBigO_psi_sub_theta_sqrt
  结论: IsBigO atTop (ψ - θ) sqrt
  证明: by
  simp_rw [isBigO_iff, Pi.sub_apply, norm_eq_abs, eventually_atTop]
  obtain ⟨C, hC⟩ := psi_sub_theta_le_mul_sqrt
  refine ⟨C, 0, fun x _ => ?_⟩
  have := theta_le_psi x
  rw [abs_of_nonneg (by positivity)]; rw [abs_of_nonneg (by positivity)]
  exact hC x

Depends on / 依赖: Pi.sub_apply, abs_of_nonneg, eventually_atTop, isBigO_iff, norm_eq_abs, psi_sub_theta_le_mul_sqrt, simp_rw, sub_apply, theta_le_psi
-/
theorem isBigO_psi_sub_theta_sqrt : IsBigO atTop (ψ - θ) sqrt := by
  simp_rw [isBigO_iff, Pi.sub_apply, norm_eq_abs, eventually_atTop]
  obtain ⟨C, hC⟩ := psi_sub_theta_le_mul_sqrt
  refine ⟨C, 0, fun x _ => ?_⟩
  have := theta_le_psi x
  rw [abs_of_nonneg (by positivity)]; rw [abs_of_nonneg (by positivity)]
  exact hC x

end CostaPereira

section PrimeCounting

/-! ## Relation to prime counting

We relate `θ` to the prime counting function `π`.-/

open Asymptotics Filter MeasureTheory

/--
theorem `integrableOn_theta_div_id_mul_log_sq` / 定理 `integrableOn_theta_div_id_mul_log_sq`

English:
theorem integrableOn_theta_div_id_mul_log_sq
  given: (x : Real)
  proof: by
  conv => arg 1; ext; rw [theta, div_eq_mul_one_div, mul_comm, sum_filter]
refine integrableOn_mul_sum_Icc _ (by norm_num) ContinuousOn.integrableOn_Icc fun x hx =>
    ContinuousAt.continuousWithinAt ?_
  have : x != 0 := by linarith [hx.1]
have : x * log x ^ 2 != 0 := mul_ne_zero this by simp; 

中文:
定理 integrableOn_theta_div_id_mul_log_sq
  条件: (x : 实数)
  证明: by
  conv => arg 1; ext; rw [theta, div_eq_mul_one_div, mul_comm, sum_filter]
refine integrableOn_mul_sum_Icc _ (by norm_num) ContinuousOn.integrableOn_Icc fun x hx =>
    ContinuousAt.continuousWithinAt ?_
  have : x != 0 := by linarith [hx.1]
have : x * log x ^ 2 != 0 := mul_ne_zero this by simp; 

Depends on / 依赖: ContinuousAt, ContinuousAt.continuousWithinAt, ContinuousOn, ContinuousOn.integrableOn_Icc, continuousWithinAt, div_eq_mul_one_div, fun_prop, integrableOn_Icc, integrableOn_mul_sum_Icc, mul_comm, mul_ne_zero, sum_filter
-/
theorem integrableOn_theta_div_id_mul_log_sq (x : Real) :
    IntegrableOn (fun t => θ t / (t * log t ^ 2)) (Set.Icc 2 x) volume := by
  conv => arg 1; ext; rw [theta, div_eq_mul_one_div, mul_comm, sum_filter]
refine integrableOn_mul_sum_Icc _ (by norm_num) ContinuousOn.integrableOn_Icc fun x hx =>
    ContinuousAt.continuousWithinAt ?_
  have : x != 0 := by linarith [hx.1]
have : x * log x ^ 2 != 0 := mul_ne_zero this by simp; grind
  fun_prop

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `primeCounting_eq_theta_div_log_add_integral` / 定理 `primeCounting_eq_theta_div_log_add_integral`

English:
theorem primeCounting_eq_theta_div_log_add_integral
  given: {x : Real} (hx : 2 <= x)
  proof: by
  -- Rewrite in a form to which Abel summation can be applied
  simp only [primeCounting, primeCounting', count_eq_card_filter_range]
  rw [card_eq_sum_ones]; rw [range_succ_eq_Icc_zero]; rw [sum_filter]
  push_cast
  let a : Nat -> Real := Set.indicator (Set.ofPred Nat.Prime) (fun n => log n)
  

中文:
定理 primeCounting_eq_theta_div_log_add_integral
  条件: {x : 实数} (hx : 2 <= x)
  证明: by
  -- Rewrite in a form to which Abel summation can be applied
  simp only [primeCounting, primeCounting', count_eq_card_filter_range]
  rw [card_eq_sum_ones]; rw [range_succ_eq_Icc_zero]; rw [sum_filter]
  push_cast
  let a : Nat -> Real := Set.indicator (Set.ofPred Nat.Prime) (fun n => log n)
  
-/
theorem primeCounting_eq_theta_div_log_add_integral {x : Real} (hx : 2 <= x) :
    π ⌊x⌋₊ = θ x / log x + ∫ t in 2..x, θ t / (t * log t ^ 2) := by
  -- Rewrite in a form to which Abel summation can be applied
  simp only [primeCounting, primeCounting', count_eq_card_filter_range]
  rw [card_eq_sum_ones]; rw [range_succ_eq_Icc_zero]; rw [sum_filter]
  push_cast
  let a : Nat -> Real := Set.indicator (Set.ofPred Nat.Prime) (fun n => log n)
  trans ∑ n in Icc 0 ⌊x⌋₊, (log n)⁻¹ * a n
  · refine sum_congr rfl fun n hn => ?_
    split_ifs with h
    · have : log n != 0 := log_ne_zero_of_pos_of_ne_one (mod_cast h.pos) (mod_cast h.ne_one)
      simp [a, h, field]
    · simp [a, h]
  rw [sum_mul_eq_sub_integral_mul₁ a (f := fun n => (log n)⁻¹) (by simp [a]) (by simp [a]),
    ← intervalIntegral.integral_of_le hx]
  · -- Rewrite the derivative inside the integral
    have int_deriv (f : Real -> Real) :
        ∫ u in 2..x, deriv (fun x => (log x)⁻¹) u * f u =
        ∫ u in 2..x, f u * -(u * log u ^ 2)⁻¹ :=
      intervalIntegral.integral_congr fun u _ => by simp [field]
    rw [int_deriv]
    simp [a, Set.indicator_apply, sum_filter, theta_eq_sum_Icc]
    grind
  · -- Differentiability
    intro z ⟨_, _⟩
    have : z != 0 := by linarith
    have : log z != 0 := by apply log_ne_zero_of_pos_of_ne_one <;> linarith
    fun_prop
  · -- Integrability of the derivative
    refine ContinuousOn.integrableOn_Icc fun z ⟨_, _⟩ => ContinuousWithinAt.congr ?_
      (fun _ _ => deriv_inv_log_apply) deriv_inv_log_apply
    have : z != 0 := by linarith
    have : log z ^ 2 != 0 := by
refine pow_ne_zero 2 log_ne_zero_of_pos_of_ne_one ?_ ?_ <;> linarith
exact ContinuousAt.continuousWithinAt by fun_prop

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `theta_eq_primeCounting_mul_log_sub_integral` / 定理 `theta_eq_primeCounting_mul_log_sub_integral`

English:
theorem theta_eq_primeCounting_mul_log_sub_integral
  given: {x : Real} (hx : 2 <= x)
  proof: by
  -- Rewrite in a form to which Abel summation can be applied
  rw [theta_eq_sum_Icc]; rw [sum_filter]
  let a : Nat -> Real := Set.indicator (Set.ofPred Nat.Prime) (fun n => 1)
  trans ∑ n in Icc 0 ⌊x⌋₊, log n * a n
  · refine sum_congr rfl fun n _ => ?_
    split_ifs with h <;> simp [a, h]
  rw

中文:
定理 theta_eq_primeCounting_mul_log_sub_integral
  条件: {x : 实数} (hx : 2 <= x)
  证明: by
  -- Rewrite in a form to which Abel summation can be applied
  rw [theta_eq_sum_Icc]; rw [sum_filter]
  let a : Nat -> Real := Set.indicator (Set.ofPred Nat.Prime) (fun n => 1)
  trans ∑ n in Icc 0 ⌊x⌋₊, log n * a n
  · refine sum_congr rfl fun n _ => ?_
    split_ifs with h <;> simp [a, h]
  rw
-/
theorem theta_eq_primeCounting_mul_log_sub_integral {x : Real} (hx : 2 <= x) :
    θ x = π ⌊x⌋₊ * log x - ∫ t in 2..x, π ⌊t⌋₊ / t := by
  -- Rewrite in a form to which Abel summation can be applied
  rw [theta_eq_sum_Icc]; rw [sum_filter]
  let a : Nat -> Real := Set.indicator (Set.ofPred Nat.Prime) (fun n => 1)
  trans ∑ n in Icc 0 ⌊x⌋₊, log n * a n
  · refine sum_congr rfl fun n _ => ?_
    split_ifs with h <;> simp [a, h]
  rw [sum_mul_eq_sub_integral_mul₁ a (by simp [a]; rw [not_prime_zero])
    (by simp [a, not_prime_one]) _ (fun z ⟨hz, _⟩ => (by fun_prop (disch := linarith))) ?hint,
    ← intervalIntegral.integral_of_le hx]
  case hint =>
    rw [deriv_log']
    refine ContinuousOn.integrableOn_Icc ?_
    fun_prop (disch := grind)
  -- Rewrite the derivative inside the integral
  simp only [primeCounting, primeCounting', count_eq_card_filter_range]
  have int_deriv (f : Real -> Real) :
      ∫ u in 2..x, deriv (fun x => log x) u * f u =
      ∫ u in 2..x, f u / u :=
    intervalIntegral.integral_congr fun u _ => by rw [deriv_log, mul_comm, div_eq_mul_inv]
  rw [int_deriv]
  simp [a, Set.indicator_apply, range_succ_eq_Icc_zero, mul_comm]

/--
theorem `intervalIntegrable_one_div_log_sq` / 定理 `intervalIntegrable_one_div_log_sq`

English:
theorem intervalIntegrable_one_div_log_sq
  given: {a b : Real} (one_lt_a : 1 < a) (one_lt_b : 1 < b)
  proof: by
  refine ContinuousOn.intervalIntegrable fun x hx => ContinuousAt.continuousWithinAt ?_
  rw [Set.mem_uIcc] at hx
  have : x != 0 := by grind
  have : log x ^ 2 != 0 := pow_ne_zero _ (log_ne_zero.mpr (by grind))
  fun_prop

中文:
定理 intervalIntegrable_one_div_log_sq
  条件: {a b : 实数} (one_lt_a : 1 < a) (one_lt_b : 1 < b)
  证明: by
  refine ContinuousOn.intervalIntegrable fun x hx => ContinuousAt.continuousWithinAt ?_
  rw [Set.mem_uIcc] at hx
  have : x != 0 := by grind
  have : log x ^ 2 != 0 := pow_ne_zero _ (log_ne_zero.mpr (by grind))
  fun_prop

Depends on / 依赖: ContinuousAt, ContinuousAt.continuousWithinAt, ContinuousOn, ContinuousOn.intervalIntegrable, Set.mem_uIcc, continuousWithinAt, fun_prop, intervalIntegrable, log_ne_zero, log_ne_zero.mpr, mem_uIcc, pow_ne_zero
-/
theorem intervalIntegrable_one_div_log_sq {a b : Real} (one_lt_a : 1 < a) (one_lt_b : 1 < b) :
    IntervalIntegrable (fun x => 1 / log x ^ 2) MeasureTheory.volume a b := by
  refine ContinuousOn.intervalIntegrable fun x hx => ContinuousAt.continuousWithinAt ?_
  rw [Set.mem_uIcc] at hx
  have : x != 0 := by grind
  have : log x ^ 2 != 0 := pow_ne_zero _ (log_ne_zero.mpr (by grind))
  fun_prop

/--
theorem `integral_1_div_log_sq_le` / 定理 `integral_1_div_log_sq_le`

English:
theorem integral_1_div_log_sq_le
  given: {a b : Real} (hab : a <= b) (one_lt : 1 < a)
  proof: by
  calc
  _ <= ∫ x in a..b, 1 / log a ^ 2 := by
      refine intervalIntegral.integral_mono_on hab ?_ (by simp) fun x ⟨_, _⟩ => by gcongr <;> bound
      apply intervalIntegrable_one_div_log_sq <;> linarith
  _ <= _ := by simp [field]

中文:
定理 integral_1_div_log_sq_le
  条件: {a b : 实数} (hab : a <= b) (one_lt : 1 < a)
  证明: by
  calc
  _ <= ∫ x in a..b, 1 / log a ^ 2 := by
      refine intervalIntegral.integral_mono_on hab ?_ (by simp) fun x ⟨_, _⟩ => by gcongr <;> bound
      apply intervalIntegrable_one_div_log_sq <;> linarith
  _ <= _ := by simp [field]
-/
private theorem integral_1_div_log_sq_le {a b : Real} (hab : a <= b) (one_lt : 1 < a) :
    ∫ x in a..b, 1 / log x ^ 2 <= (b - a) / log a ^ 2 := by
  calc
  _ <= ∫ x in a..b, 1 / log a ^ 2 := by
      refine intervalIntegral.integral_mono_on hab ?_ (by simp) fun x ⟨_, _⟩ => by gcongr <;> bound
      apply intervalIntegrable_one_div_log_sq <;> linarith
  _ <= _ := by simp [field]

/--
theorem `integral_one_div_log_sq_le_explicit` / 定理 `integral_one_div_log_sq_le_explicit`

English:
theorem integral_one_div_log_sq_le_explicit
  given: {x : Real} (hx : 4 <= x)
  proof: by
have two_le_sqrt : 2 <= x.sqrt := le_sqrt_of_sq_le by norm_num [hx]
.mpr (by bound) have sqrt_le_x : x.sqrt <= x := sqrt_le_left (by linarith)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := x.sqrt)]
  · grw [integral_1_div_log_sq_le two_le_sqrt (by linarith),
      integral_1_div_

中文:
定理 integral_one_div_log_sq_le_explicit
  条件: {x : 实数} (hx : 4 <= x)
  证明: by
have two_le_sqrt : 2 <= x.sqrt := le_sqrt_of_sq_le by norm_num [hx]
.mpr (by bound) have sqrt_le_x : x.sqrt <= x := sqrt_le_left (by linarith)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := x.sqrt)]
  · grw [integral_1_div_log_sq_le two_le_sqrt (by linarith),
      integral_1_div_
-/
private theorem integral_one_div_log_sq_le_explicit {x : Real} (hx : 4 <= x) :
    ∫ t in 2..x, 1 / log t ^ 2 <= 4 * x / (log x) ^ 2 + x.sqrt / log 2 ^ 2 := by
have two_le_sqrt : 2 <= x.sqrt := le_sqrt_of_sq_le by norm_num [hx]
.mpr (by bound) have sqrt_le_x : x.sqrt <= x := sqrt_le_left (by linarith)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := x.sqrt)]
  · grw [integral_1_div_log_sq_le two_le_sqrt (by linarith),
      integral_1_div_log_sq_le sqrt_le_x (by linarith)]
    rw [log_sqrt (by linarith)]; rw [add_comm]; rw [div_pow]; rw [← div_mul]; rw [mul_comm]; rw [mul_div_assoc]
    norm_num
    gcongr <;> linarith
  all_goals apply intervalIntegrable_one_div_log_sq <;> linarith

/--
theorem `sqrt_isLittleO` / 定理 `sqrt_isLittleO`

English:
theorem sqrt_isLittleO
  proof: by
.mp apply isLittleO_mul_iff_isLittleO_div _
  · conv => arg 2; ext; rw [mul_comm]
.mpr apply isLittleO_mul_iff_isLittleO_div _
    · simp_rw [div_sqrt, sqrt_eq_rpow, ← rpow_two]
      apply isLittleO_log_rpow_rpow_atTop _ (by norm_num)
    filter_upwards [eventually_gt_atTop 0] with x hx using sq

中文:
定理 sqrt_isLittleO
  证明: by
.mp apply isLittleO_mul_iff_isLittleO_div _
  · conv => arg 2; ext; rw [mul_comm]
.mpr apply isLittleO_mul_iff_isLittleO_div _
    · simp_rw [div_sqrt, sqrt_eq_rpow, ← rpow_two]
      apply isLittleO_log_rpow_rpow_atTop _ (by norm_num)
    filter_upwards [eventually_gt_atTop 0] with x hx using sq
-/
private theorem sqrt_isLittleO :
    Real.sqrt =o[atTop] (fun x => x / log x ^ 2) := by
.mp apply isLittleO_mul_iff_isLittleO_div _
  · conv => arg 2; ext; rw [mul_comm]
.mpr apply isLittleO_mul_iff_isLittleO_div _
    · simp_rw [div_sqrt, sqrt_eq_rpow, ← rpow_two]
      apply isLittleO_log_rpow_rpow_atTop _ (by norm_num)
    filter_upwards [eventually_gt_atTop 0] with x hx using sqrt_ne_zero'.mpr hx
  filter_upwards [eventually_gt_atTop 1] with x _
apply pow_ne_zero _ log_ne_zero.mpr ⟨_, _, _⟩ <;> linarith

/--
theorem `integral_one_div_log_sq_isBigO` / 定理 `integral_one_div_log_sq_isBigO`

English:
theorem integral_one_div_log_sq_isBigO
  proof: by
  trans (fun x => 4 * x / log x ^ 2 + √x / log 2 ^ 2)
  · apply IsBigO.of_bound'
    filter_upwards [eventually_ge_atTop 4] with x hx
apply le_trans intervalIntegral.abs_integral_le_integral_abs (by linarith)
    rw [intervalIntegral.integral_congr (g := (fun t => 1 / log t ^ 2))]
    · grw [inte

中文:
定理 integral_one_div_log_sq_isBigO
  证明: by
  trans (fun x => 4 * x / log x ^ 2 + √x / log 2 ^ 2)
  · apply IsBigO.of_bound'
    filter_upwards [eventually_ge_atTop 4] with x hx
apply le_trans intervalIntegral.abs_integral_le_integral_abs (by linarith)
    rw [intervalIntegral.integral_congr (g := (fun t => 1 / log t ^ 2))]
    · grw [inte

Depends on / 依赖: IsBigO, IsBigO.add, IsBigO.of_bound, abs_integral_le_integral_abs, eventually_ge_atTop, filter_upwards, integral_congr, integral_one_div_log_sq_le_explicit, intervalIntegral, intervalIntegral.abs_integral_le_integral_abs, intervalIntegral.integral_congr, isBigO_const_mul_self, le_trans, mul_comm, mul_div_assoc, mul_one_div, norm_of_nonneg, of_bound, simp_rw
-/
theorem integral_one_div_log_sq_isBigO :
    (fun x => ∫ t in 2..x, 1 / log t ^ 2) =O[atTop] (fun x => x / log x ^ 2) := by
  trans (fun x => 4 * x / log x ^ 2 + √x / log 2 ^ 2)
  · apply IsBigO.of_bound'
    filter_upwards [eventually_ge_atTop 4] with x hx
apply le_trans intervalIntegral.abs_integral_le_integral_abs (by linarith)
    rw [intervalIntegral.integral_congr (g := (fun t => 1 / log t ^ 2))]
    · grw [integral_one_div_log_sq_le_explicit hx, norm_of_nonneg]
      positivity
    intro t ht
    simp
  refine IsBigO.add ?_ ?_
  · simp_rw [mul_div_assoc]
    apply isBigO_const_mul_self
  conv => arg 2; ext; rw [← mul_one_div, mul_comm]
  apply IsBigO.const_mul_left sqrt_isLittleO.isBigO

/--
theorem `integral_theta_div_log_sq_isBigO` / 定理 `integral_theta_div_log_sq_isBigO`

English:
theorem integral_theta_div_log_sq_isBigO
  proof: by
  refine (IsBigO.of_bound (log 4) ?_).trans integral_one_div_log_sq_isBigO
  filter_upwards [eventually_ge_atTop 4] with x _
  simp_rw [norm_eq_abs]
  calc |∫ (t : Real) in 2..x, θ t / (t * log t ^ 2)|
    _ <= ∫ (x : Real) in 2..x, |θ x / (x * log x ^ 2)| :=
        intervalIntegral.abs_integral

中文:
定理 integral_theta_div_log_sq_isBigO
  证明: by
  refine (IsBigO.of_bound (log 4) ?_).trans integral_one_div_log_sq_isBigO
  filter_upwards [eventually_ge_atTop 4] with x _
  simp_rw [norm_eq_abs]
  calc |∫ (t : Real) in 2..x, θ t / (t * log t ^ 2)|
    _ <= ∫ (x : Real) in 2..x, |θ x / (x * log x ^ 2)| :=
        intervalIntegral.abs_integral

Depends on / 依赖: IsBigO, IsBigO.of_bound, abs_integral_le_integral_abs, eventually_ge_atTop, filter_upwards, integral_mono_on, integral_one_div_log_sq_isBigO, intervalIntegral, intervalIntegral.abs_integral_le_integral_abs, intervalIntegral.integral_mono_on, norm_eq_abs, of_bound, simp_rw
-/
theorem integral_theta_div_log_sq_isBigO :
    (fun x => ∫ t in 2..x, θ t / (t * log t ^ 2)) =O[atTop] (fun x => x / log x ^ 2) := by
  refine (IsBigO.of_bound (log 4) ?_).trans integral_one_div_log_sq_isBigO
  filter_upwards [eventually_ge_atTop 4] with x _
  simp_rw [norm_eq_abs]
  calc |∫ (t : Real) in 2..x, θ t / (t * log t ^ 2)|
    _ <= ∫ (x : Real) in 2..x, |θ x / (x * log x ^ 2)| :=
        intervalIntegral.abs_integral_le_integral_abs (by linarith)
    _ <= ∫ (x : Real) in 2..x, log 4 * (1 / log x ^ 2) :=
        intervalIntegral.integral_mono_on (by linarith) ?hf ?hg fun t ⟨ht, _⟩ => ?hh
    _ = log 4 * |∫ (t : Real) in 2..x, 1 / log t ^ 2| := by
        rw [intervalIntegral.integral_const_mul]; rw [abs_of_nonneg]
        exact intervalIntegral.integral_nonneg (by linarith) fun u _ => by positivity
  case hf =>
    refine (intervalIntegrable_iff.mpr ?_).abs
    rw [Set.uIoc_of_le (by linarith)]; rw [← integrableOn_Icc_iff_integrableOn_Ioc]
    exact integrableOn_theta_div_id_mul_log_sq x
  case hg =>
    refine (intervalIntegrable_one_div_log_sq ?_ ?_).const_mul _ <;> linarith
  case hh =>
    calc |θ t / (t * log t ^ 2)|
    _ = θ t / (t * log t ^ 2) := abs_of_nonneg (by positivity [theta_nonneg t])
    _ <= log 4 * t / (t * log t ^ 2) := by grw [theta_le_log4_mul_x (by linarith)]
    _ = log 4 * (1 / log t ^ 2) := by field

/--
theorem `integral_theta_div_log_sq_isLittleO` / 定理 `integral_theta_div_log_sq_isLittleO`

English:
theorem integral_theta_div_log_sq_isLittleO
  proof: by
  refine integral_theta_div_log_sq_isBigO.trans_isLittleO ?_
.mpr ?_ refine isLittleO_iff_tendsto' (by simp)
  refine Tendsto.congr' (f₁ := fun x => (log x)⁻¹) ?_ tendsto_log_atTop.inv_tendsto_atTop
  filter_upwards [eventually_gt_atTop 0] with x _
  field

中文:
定理 integral_theta_div_log_sq_isLittleO
  证明: by
  refine integral_theta_div_log_sq_isBigO.trans_isLittleO ?_
.mpr ?_ refine isLittleO_iff_tendsto' (by simp)
  refine Tendsto.congr' (f₁ := fun x => (log x)⁻¹) ?_ tendsto_log_atTop.inv_tendsto_atTop
  filter_upwards [eventually_gt_atTop 0] with x _
  field

Depends on / 依赖: Tendsto, Tendsto.congr, eventually_gt_atTop, filter_upwards, integral_theta_div_log_sq_isBigO, integral_theta_div_log_sq_isBigO.trans_isLittleO, inv_tendsto_atTop, isLittleO_iff_tendsto, tendsto_log_atTop, tendsto_log_atTop.inv_tendsto_atTop, trans_isLittleO
-/
theorem integral_theta_div_log_sq_isLittleO :
    (fun x => ∫ t in 2..x, θ t / (t * log t ^ 2)) =o[atTop] (fun x => x / log x) := by
  refine integral_theta_div_log_sq_isBigO.trans_isLittleO ?_
.mpr ?_ refine isLittleO_iff_tendsto' (by simp)
  refine Tendsto.congr' (f₁ := fun x => (log x)⁻¹) ?_ tendsto_log_atTop.inv_tendsto_atTop
  filter_upwards [eventually_gt_atTop 0] with x _
  field

/--
theorem `primeCounting_sub_theta_div_log_isBigO` / 定理 `primeCounting_sub_theta_div_log_isBigO`

English:
theorem primeCounting_sub_theta_div_log_isBigO
  proof: by
  apply integral_theta_div_log_sq_isBigO.congr' _ (by rfl)
  filter_upwards [eventually_ge_atTop 2] with x hx
  rw [primeCounting_eq_theta_div_log_add_integral hx]
  simp

中文:
定理 primeCounting_sub_theta_div_log_isBigO
  证明: by
  apply integral_theta_div_log_sq_isBigO.congr' _ (by rfl)
  filter_upwards [eventually_ge_atTop 2] with x hx
  rw [primeCounting_eq_theta_div_log_add_integral hx]
  simp

Depends on / 依赖: eventually_ge_atTop, filter_upwards, integral_theta_div_log_sq_isBigO, integral_theta_div_log_sq_isBigO.congr, primeCounting_eq_theta_div_log_add_integral
-/
theorem primeCounting_sub_theta_div_log_isBigO :
    (fun x => π ⌊x⌋₊ - θ x / log x) =O[atTop] (fun x => x / log x ^ 2) := by
  apply integral_theta_div_log_sq_isBigO.congr' _ (by rfl)
  filter_upwards [eventually_ge_atTop 2] with x hx
  rw [primeCounting_eq_theta_div_log_add_integral hx]
  simp

/--
theorem `eventually_primeCounting_le` / 定理 `eventually_primeCounting_le`

English:
theorem eventually_primeCounting_le
  given: {ε : Real} (εpos : 0 < ε)
  proof: by
  have := integral_theta_div_log_sq_isLittleO.bound εpos
  filter_upwards [eventually_ge_atTop 2, this] with x hx hx2
  rw [primeCounting_eq_theta_div_log_add_integral hx]; rw [add_mul]; rw [add_div]
  have : 0 <= log x := by bound
  rw [norm_of_nonneg (show 0 <= x / log x by bound)]; rw [← mul_d

中文:
定理 eventually_primeCounting_le
  条件: {ε : 实数} (εpos : 0 < ε)
  证明: by
  have := integral_theta_div_log_sq_isLittleO.bound εpos
  filter_upwards [eventually_ge_atTop 2, this] with x hx hx2
  rw [primeCounting_eq_theta_div_log_add_integral hx]; rw [add_mul]; rw [add_div]
  have : 0 <= log x := by bound
  rw [norm_of_nonneg (show 0 <= x / log x by bound)]; rw [← mul_d

Depends on / 依赖: add_div, add_mul, eventually_ge_atTop, filter_upwards, integral_theta_div_log_sq_isLittleO, integral_theta_div_log_sq_isLittleO.bound, le_norm_self, mul_div_assoc, norm_of_nonneg, primeCounting_eq_theta_div_log_add_integral, theta_le_log4_mul_x
-/
theorem eventually_primeCounting_le {ε : Real} (εpos : 0 < ε) :
    forallᶠ x in atTop, π ⌊x⌋₊ <= (log 4 + ε) * x / log x := by
  have := integral_theta_div_log_sq_isLittleO.bound εpos
  filter_upwards [eventually_ge_atTop 2, this] with x hx hx2
  rw [primeCounting_eq_theta_div_log_add_integral hx]; rw [add_mul]; rw [add_div]
  have : 0 <= log x := by bound
  rw [norm_of_nonneg (show 0 <= x / log x by bound)]; rw [← mul_div_assoc] at hx2
  grw [theta_le_log4_mul_x (by linarith), ← hx2]
  grind [le_norm_self]

/--
theorem `pi_ge` / 定理 `pi_ge`

English:
theorem pi_ge
  given: (n : Nat)
  statement: (n * log 2 - log (n + 1)) / log n <= π n
  proof: by
  rcases (show n = 0 ∨ n = 1 ∨ 1 < n by lia) with rfl | rfl | h
  · simp
  · simp
  grw [div_le_iff₀ (log_pos (mod_cast h)), ← psi_le_primeCounting_mul_log, psi_ge]

中文:
定理 pi_ge
  条件: (n : 自然数)
  结论: (n * log 2 - log (n + 1)) / log n <= π n
  证明: by
  rcases (show n = 0 ∨ n = 1 ∨ 1 < n by lia) with rfl | rfl | h
  · simp
  · simp
  grw [div_le_iff₀ (log_pos (mod_cast h)), ← psi_le_primeCounting_mul_log, psi_ge]

Depends on / 依赖: log_pos, mod_cast, psi_ge, psi_le_primeCounting_mul_log
-/
theorem pi_ge (n : Nat) : (n * log 2 - log (n + 1)) / log n <= π n := by
  rcases (show n = 0 ∨ n = 1 ∨ 1 < n by lia) with rfl | rfl | h
  · simp
  · simp
  grw [div_le_iff₀ (log_pos (mod_cast h)), ← psi_le_primeCounting_mul_log, psi_ge]

/--
theorem `pi_ge'` / 定理 `pi_ge'`

English:
theorem pi_ge'
  given: {x : Real} (hx : 1 < x)
  proof: by
  grw [div_le_iff₀ (log_pos hx), ← psi_le_primeCounting_mul_log', psi_ge']
  positivity

中文:
定理 pi_ge'
  条件: {x : 实数} (hx : 1 < x)
  证明: by
  grw [div_le_iff₀ (log_pos hx), ← psi_le_primeCounting_mul_log', psi_ge']
  positivity

Depends on / 依赖: log_pos, psi_ge, psi_le_primeCounting_mul_log
-/
theorem pi_ge' {x : Real} (hx : 1 < x) :
    ((x - 1) * log 2 - log (x + 2)) / log x <= π ⌊x⌋₊ := by
  grw [div_le_iff₀ (log_pos hx), ← psi_le_primeCounting_mul_log', psi_ge']
  positivity

/--
theorem `theta_le_pi_mul_log` / 定理 `theta_le_pi_mul_log`

English:
theorem theta_le_pi_mul_log
  given: (n : Nat)
  statement: θ n <= (π n) * log n
  proof: (theta_le_psi n).trans (psi_le_primeCounting_mul_log n)

中文:
定理 theta_le_pi_mul_log
  条件: (n : 自然数)
  结论: θ n <= (π n) * log n
  证明: (theta_le_psi n).trans (psi_le_primeCounting_mul_log n)

Depends on / 依赖: psi_le_primeCounting_mul_log, theta_le_psi
-/
theorem theta_le_pi_mul_log (n : Nat) : θ n <= (π n) * log n :=
  (theta_le_psi n).trans (psi_le_primeCounting_mul_log n)

/--
theorem `theta_le_pi_mul_log'` / 定理 `theta_le_pi_mul_log'`

English:
theorem theta_le_pi_mul_log'
  given: (x : Real)
  statement: θ x <= (π ⌊x⌋₊) * log x
  proof: by
  grw [← psi_le_primeCounting_mul_log', theta_le_psi]

中文:
定理 theta_le_pi_mul_log'
  条件: (x : 实数)
  结论: θ x <= (π ⌊x⌋₊) * log x
  证明: by
  grw [← psi_le_primeCounting_mul_log', theta_le_psi]

Depends on / 依赖: psi_le_primeCounting_mul_log, theta_le_psi
-/
theorem theta_le_pi_mul_log' (x : Real) : θ x <= (π ⌊x⌋₊) * log x := by
  grw [← psi_le_primeCounting_mul_log', theta_le_psi]

/--
theorem `pi_mul_log_sqrt_le` / 定理 `pi_mul_log_sqrt_le`

English:
theorem pi_mul_log_sqrt_le
  given: {x : Real} (hx : 1 <= x)
  proof: calc
  _ = ∑ p in primesLE ⌊x⌋₊, log √x := by simp
  _ <= ∑ p in primesLE ⌊x⌋₊, (log p + (if p <= √x then log √x else 0)) := by
    refine sum_le_sum fun p _ => ?_
    split_ifs with h
    · simp [log_natCast_nonneg]
    have : log √x < log p := log_lt_log (by positivity) (not_le.mp h)
    grind
  _

中文:
定理 pi_mul_log_sqrt_le
  条件: {x : 实数} (hx : 1 <= x)
  证明: calc
  _ = ∑ p in primesLE ⌊x⌋₊, log √x := by simp
  _ <= ∑ p in primesLE ⌊x⌋₊, (log p + (if p <= √x then log √x else 0)) := by
    refine sum_le_sum fun p _ => ?_
    split_ifs with h
    · simp [log_natCast_nonneg]
    have : log √x < log p := log_lt_log (by positivity) (not_le.mp h)
    grind
  _
-/
private theorem pi_mul_log_sqrt_le {x : Real} (hx : 1 <= x) :
    (π ⌊x⌋₊) * log √x <= log 4 * x + √x * log √x := calc
  _ = ∑ p in primesLE ⌊x⌋₊, log √x := by simp
  _ <= ∑ p in primesLE ⌊x⌋₊, (log p + (if p <= √x then log √x else 0)) := by
    refine sum_le_sum fun p _ => ?_
    split_ifs with h
    · simp [log_natCast_nonneg]
    have : log √x < log p := log_lt_log (by positivity) (not_le.mp h)
    grind
  _ <= _ := by
    grw [← theta_le_log4_mul_x (by positivity)]
    rw [sum_add_distrib]; rw [theta_eq_theta_coe_floor]; rw [theta_eq_sum_primesLE_log]; rw [← sum_filter]
    simp only [sum_const, nsmul_eq_mul]
    gcongr
    · exact log_nonneg (one_le_sqrt.mpr hx)
refine le_trans ?_ floor_le (sqrt_nonneg x)
    norm_cast
    rw [show ⌊√x⌋₊ = #(Icc 1 ⌊√x⌋₊) by simp]
    refine card_le_card fun p hp => ?_
    simp only [mem_filter, mem_Icc, mem_primesLE] at hp ⊢
    exact ⟨hp.1.2.one_le, le_floor hp.2⟩

/--
theorem `pi_le_log4_mul_div` / 定理 `pi_le_log4_mul_div`

English:
theorem pi_le_log4_mul_div
  given: {x : Real} (hx : 1 < x)
  statement: π ⌊x⌋₊ <= log 4 * x / log √x + √x
  proof: by
  have : 0 < log √x := log_pos (lt_sqrt_of_sq_lt (by simp [hx]))
  field_simp
  grind [pi_mul_log_sqrt_le hx.le]

中文:
定理 pi_le_log4_mul_div
  条件: {x : 实数} (hx : 1 < x)
  结论: π ⌊x⌋₊ <= log 4 * x / log √x + √x
  证明: by
  have : 0 < log √x := log_pos (lt_sqrt_of_sq_lt (by simp [hx]))
  field_simp
  grind [pi_mul_log_sqrt_le hx.le]

Depends on / 依赖: hx.le, log_pos, lt_sqrt_of_sq_lt, pi_mul_log_sqrt_le
-/
theorem pi_le_log4_mul_div {x : Real} (hx : 1 < x) : π ⌊x⌋₊ <= log 4 * x / log √x + √x := by
  have : 0 < log √x := log_pos (lt_sqrt_of_sq_lt (by simp [hx]))
  field_simp
  grind [pi_mul_log_sqrt_le hx.le]

end PrimeCounting
end Chebyshev

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: the first Chebyshev function is nonnegative. -/
@[positivity Chebyshev.theta _]
meta def evalTheta : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(@Chebyshev.theta $a) =>
    assertInstancesCommute
    pure (.nonnegative q(Chebyshev.theta_nonneg $a))
  | _, _, _ => throwError "not theta"

/-- Extension for the `positivity` tactic: the second Chebyshev function is nonnegative. -/
@[positivity Chebyshev.psi _]
meta def evalPsi : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(@Chebyshev.psi $a) =>
    assertInstancesCommute
    pure (.nonnegative q(Chebyshev.psi_nonneg $a))
  | _, _, _ => throwError "not psi"

end Mathlib.Meta.Positivity
