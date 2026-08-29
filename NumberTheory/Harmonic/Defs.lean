/-
Copyright (c) 2023 Koundinya Vajjha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Koundinya Vajjha, Thomas Browning
-/
module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!

This file defines the harmonic numbers.

* `Mathlib/NumberTheory/Harmonic/Int.lean` proves that the `n`th harmonic number is not an integer.
* `Mathlib/NumberTheory/Harmonic/Bounds.lean` provides basic log bounds.

-/

@[expose] public section

/--
Definition of `harmonic` / `harmonic` 的定义

English:
definition harmonic
  signature: : Nat -> Rat
  body: fun n => ∑ i in Finset.range n, (↑(i + 1))⁻¹

@[simp]

中文:
定义 harmonic
  签名: : 自然数 -> Rat
  定义体: fun n => ∑ i in Finset.range n, (↑(i + 1))⁻¹

@[simp]

Depends on / 依赖: Finset, Finset.range
-/
def harmonic : Nat -> Rat := fun n => ∑ i in Finset.range n, (↑(i + 1))⁻¹

@[simp]
/--
lemma `harmonic_zero` / 引理 `harmonic_zero`

English:
lemma harmonic_zero
  statement: harmonic 0 = 0
  proof: rfl

@[simp]

中文:
引理 harmonic_zero
  结论: harmonic 0 = 0
  证明: rfl

@[simp]
-/
lemma harmonic_zero : harmonic 0 = 0 :=
  rfl

@[simp]
/--
lemma `harmonic_succ` / 引理 `harmonic_succ`

English:
lemma harmonic_succ
  given: (n : Nat)
  statement: harmonic (n + 1) = harmonic n + (↑(n + 1))⁻¹
  proof: Finset.sum_range_succ ..

中文:
引理 harmonic_succ
  条件: (n : 自然数)
  结论: harmonic (n + 1) = harmonic n + (↑(n + 1))⁻¹
  证明: Finset.sum_range_succ ..

Depends on / 依赖: Finset, Finset.sum_range_succ, sum_range_succ
-/
lemma harmonic_succ (n : Nat) : harmonic (n + 1) = harmonic n + (↑(n + 1))⁻¹ :=
  Finset.sum_range_succ ..
