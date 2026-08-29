/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Derivatives of `x ^ m`, `m : ℤ` within an open set

In this file we prove theorems about iterated derivatives of `x ^ m`, `m : ℤ` within an open set.

## Keywords

iterated, derivative, power, open set
-/

public section

open scoped Nat

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {s : Set 𝕜}

/--
theorem `iteratedDerivWithin_zpow` / 定理 `iteratedDerivWithin_zpow`

English:
theorem iteratedDerivWithin_zpow
  given: (m : Int) (k : Nat) (hs : IsOpen s)
  proof: by
  apply Set.EqOn.trans (iteratedDerivWithin_of_isOpen_eq_iterate hs)
  intro t ht
  simp

中文:
定理 iteratedDerivWithin_zpow
  条件: (m : 整数) (k : 自然数) (hs : IsOpen s)
  证明: by
  apply Set.EqOn.trans (iteratedDerivWithin_of_isOpen_eq_iterate hs)
  intro t ht
  simp

Depends on / 依赖: Set.EqOn.trans, iteratedDerivWithin_of_isOpen_eq_iterate
-/
theorem iteratedDerivWithin_zpow (m : Int) (k : Nat) (hs : IsOpen s) :
    s.EqOn (iteratedDerivWithin k (fun y => y ^ m) s)
    (fun y => (∏ i in Finset.range k, ((m : 𝕜) - i)) * y ^ (m - k)) := by
  apply Set.EqOn.trans (iteratedDerivWithin_of_isOpen_eq_iterate hs)
  intro t ht
  simp

/--
theorem `iteratedDerivWithin_one_div` / 定理 `iteratedDerivWithin_one_div`

English:
theorem iteratedDerivWithin_one_div
  given: (k : Nat) (hs : IsOpen s)
  proof: by
  apply Set.EqOn.trans (iteratedDerivWithin_of_isOpen_eq_iterate hs)
  intro t ht
  simp

中文:
定理 iteratedDerivWithin_one_div
  条件: (k : 自然数) (hs : IsOpen s)
  证明: by
  apply Set.EqOn.trans (iteratedDerivWithin_of_isOpen_eq_iterate hs)
  intro t ht
  simp

Depends on / 依赖: Set.EqOn.trans, iteratedDerivWithin_of_isOpen_eq_iterate
-/
theorem iteratedDerivWithin_one_div (k : Nat) (hs : IsOpen s) :
    s.EqOn (iteratedDerivWithin k (fun y => 1 / y) s)
    (fun y => (-1) ^ k * (k !) * (y ^ (-1 - k : Int))) := by
  apply Set.EqOn.trans (iteratedDerivWithin_of_isOpen_eq_iterate hs)
  intro t ht
  simp
