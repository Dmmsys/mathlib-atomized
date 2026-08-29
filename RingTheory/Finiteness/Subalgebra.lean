/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Bilinear

/-!
# Subalgebras that are finitely generated as submodules
-/

public section

open Function (Surjective)
open Finsupp

namespace Subalgebra

open Submodule

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/--
theorem `fg_bot_toSubmodule` / 定理 `fg_bot_toSubmodule`

English:
theorem fg_bot_toSubmodule
  statement: (⊥ : Subalgebra R A).toSubmodule.FG
  proof: ⟨{1}, by simp [Algebra.toSubmodule_bot, one_eq_span]⟩

中文:
定理 fg_bot_toSubmodule
  结论: (⊥ : Subalgebra R A).toSubmodule.FG
  证明: ⟨{1}, by simp [Algebra.toSubmodule_bot, one_eq_span]⟩

Depends on / 依赖: Algebra, Algebra.toSubmodule_bot, one_eq_span, toSubmodule_bot
-/
theorem fg_bot_toSubmodule : (⊥ : Subalgebra R A).toSubmodule.FG :=
  ⟨{1}, by simp [Algebra.toSubmodule_bot, one_eq_span]⟩

/--
Instance `finite_bot` / 实例 `finite_bot`

English:
instance finite_bot
  signature: : Module.Finite R (⊥ : Subalgebra R A)
  body: Module.Finite.range (Algebra.linearMap R A)

中文:
实例 finite_bot
  签名: : Module.Finite R (⊥ : Subalgebra R A)
  定义体: Module.Finite.range (Algebra.linearMap R A)

Depends on / 依赖: Algebra, Algebra.linearMap, Finite, Module, Module.Finite.range, linearMap
-/
instance finite_bot : Module.Finite R (⊥ : Subalgebra R A) :=
  Module.Finite.range (Algebra.linearMap R A)

end Subalgebra

namespace Submodule

/--
theorem `fg_unit` / 定理 `fg_unit`

English:
theorem fg_unit
  given: {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (I : (Submodule R A)ˣ)
  proof: by
  obtain ⟨T, T', hT, hT', one_mem⟩ := mem_span_mul_finite_of_mem_mul (I.mul_inv ▸ one_le.mp le_rfl)
  refine ⟨T, span_eq_of_le _ hT ?_⟩
  rw [← one_mul I]; rw [← mul_one (span R (T : Set A))]
  conv_rhs => rw [← I.inv_mul, ← mul_assoc]
  grw [← span_le.mpr hT', Units.val_mul, Units.val_one, span_

中文:
定理 fg_unit
  条件: {R A : 类型} [CommSemiring R] [Semiring A] [Algebra R A] (I : (Submodule R A)ˣ)
  证明: by
  obtain ⟨T, T', hT, hT', one_mem⟩ := mem_span_mul_finite_of_mem_mul (I.mul_inv ▸ one_le.mp le_rfl)
  refine ⟨T, span_eq_of_le _ hT ?_⟩
  rw [← one_mul I]; rw [← mul_one (span R (T : Set A))]
  conv_rhs => rw [← I.inv_mul, ← mul_assoc]
  grw [← span_le.mpr hT', Units.val_mul, Units.val_one, span_

Depends on / 依赖: I.inv_mul, I.mul_inv, Units.val_mul, Units.val_one, conv_rhs, inv_mul, le_rfl, mem_span_mul_finite_of_mem_mul, mul_assoc, mul_inv, mul_one, one_le, one_le.mp, one_mem, one_mul, span_eq_of_le, span_le, span_le.mpr, span_mul_span, val_mul
-/
theorem fg_unit {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (I : (Submodule R A)ˣ) :
    (I : Submodule R A).FG := by
  obtain ⟨T, T', hT, hT', one_mem⟩ := mem_span_mul_finite_of_mem_mul (I.mul_inv ▸ one_le.mp le_rfl)
  refine ⟨T, span_eq_of_le _ hT ?_⟩
  rw [← one_mul I]; rw [← mul_one (span R (T : Set A))]
  conv_rhs => rw [← I.inv_mul, ← mul_assoc]
  grw [← span_le.mpr hT', Units.val_mul, Units.val_one, span_mul_span, one_le.2 one_mem]

/--
theorem `fg_of_isUnit` / 定理 `fg_of_isUnit`

English:
theorem fg_of_isUnit
  statement: {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] {I : Submodule R A}
  proof: fg_unit hI.unit

中文:
定理 fg_of_isUnit
  结论: {R A : 类型} [CommSemiring R] [Semiring A] [Algebra R A] {I : Submodule R A}
  证明: fg_unit hI.unit

Depends on / 依赖: fg_unit, hI.unit
-/
theorem fg_of_isUnit {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] {I : Submodule R A}
    (hI : IsUnit I) : I.FG :=
  fg_unit hI.unit

section Mul

variable {R : Type*} {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
variable {M N : Submodule R A}

/--
theorem `FG.mul` / 定理 `FG.mul`

English:
theorem FG.mul
  given: (hm : M.FG) (hn : N.FG)
  statement: (M * N).FG
  proof: by
  rw [mul_eq_map₂]; exact hm.map₂ _ hn

中文:
定理 FG.mul
  条件: (hm : M.FG) (hn : N.FG)
  结论: (M * N).FG
  证明: by
  rw [mul_eq_map₂]; exact hm.map₂ _ hn
-/
theorem FG.mul (hm : M.FG) (hn : N.FG) : (M * N).FG := by
  rw [mul_eq_map₂]; exact hm.map₂ _ hn

/--
theorem `FG.pow` / 定理 `FG.pow`

English:
theorem FG.pow
  given: (h : M.FG) (n : Nat)
  statement: (M ^ n).FG
  proof: Nat.recOn n ⟨{1}, by simp [one_eq_span]⟩ fun n ih => by simpa [pow_succ] using ih.mul h

中文:
定理 FG.pow
  条件: (h : M.FG) (n : 自然数)
  结论: (M ^ n).FG
  证明: Nat.recOn n ⟨{1}, by simp [one_eq_span]⟩ fun n ih => by simpa [pow_succ] using ih.mul h
-/
theorem FG.pow (h : M.FG) (n : Nat) : (M ^ n).FG :=
  Nat.recOn n ⟨{1}, by simp [one_eq_span]⟩ fun n ih => by simpa [pow_succ] using ih.mul h

end Mul

end Submodule
