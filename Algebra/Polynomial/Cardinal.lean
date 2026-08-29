/-
Copyright (c) 2021 Chris Hughes, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Cardinal
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.SetTheory.Cardinal.Finsupp

/-!
# Cardinality of Polynomial Ring

The result in this file is that the cardinality of `R[X]` is at most the maximum
of `#R` and `ℵ₀`.
-/

public section

open Cardinal Fintype

universe u v
variable {R : Type u} {M : Type v} [Semiring R]

namespace Polynomial

@[simp]
/--
lemma `cardinalMk_eq_max` / 引理 `cardinalMk_eq_max`

English:
lemma cardinalMk_eq_max
  given: {R : Type u} [Semiring R] [Nontrivial R]
  statement: #(R[X]) = max #R ℵ₀
  proof: by
  simp [(toFinsuppIso R).toEquiv.cardinal_eq]

中文:
引理 cardinalMk_eq_max
  条件: {R : 类型u} [半环 R] [非平凡 R]
  结论: #(R[X]) = 最大值 #R ℵ₀
  证明: by
  simp [(toFinsuppIso R).toEquiv.cardinal_eq]

Depends on / 依赖: cardinal_eq, toEquiv, toEquiv.cardinal_eq, toFinsuppIso
-/
lemma cardinalMk_eq_max {R : Type u} [Semiring R] [Nontrivial R] : #(R[X]) = max #R ℵ₀ := by
  simp [(toFinsuppIso R).toEquiv.cardinal_eq]

/--
lemma `cardinalMk_le_max` / 引理 `cardinalMk_le_max`

English:
lemma cardinalMk_le_max
  given: {R : Type u} [Semiring R]
  statement: #(R[X]) <= max #R ℵ₀
  proof: by
  cases subsingleton_or_nontrivial R
  · exact (mk_eq_one _).trans_le (le_max_of_le_right one_le_aleph0)
  · exact cardinalMk_eq_max.le

中文:
引理 cardinalMk_le_max
  条件: {R : 类型u} [半环 R]
  结论: #(R[X]) <= 最大值 #R ℵ₀
  证明: by
  cases subsingleton_or_nontrivial R
  · exact (mk_eq_one _).trans_le (le_max_of_le_right one_le_aleph0)
  · exact cardinalMk_eq_max.le

Depends on / 依赖: cardinalMk_eq_max, cardinalMk_eq_max.le, le_max_of_le_right, mk_eq_one, one_le_aleph0, subsingleton_or_nontrivial, trans_le
-/
lemma cardinalMk_le_max {R : Type u} [Semiring R] : #(R[X]) <= max #R ℵ₀ := by
  cases subsingleton_or_nontrivial R
  · exact (mk_eq_one _).trans_le (le_max_of_le_right one_le_aleph0)
  · exact cardinalMk_eq_max.le

end Polynomial
