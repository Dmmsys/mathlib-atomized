/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.SetTheory.Cardinal.Basic

/-!
# Cardinality of a module

This file proves that the cardinality of a module without zero divisors is at least the cardinality
of its base ring.
-/

public section

open Function

universe u v

namespace Cardinal

/--
theorem `mk_le_of_module` / 定理 `mk_le_of_module`

English:
theorem mk_le_of_module
  statement: (R : Type u) (E : Type v)
  proof: by
  obtain ⟨x, hx⟩ : exists (x : E), x != 0 := exists_ne 0
  have : Injective (fun k => k • x) := smul_left_injective R hx
  exact lift_mk_le_lift_mk_of_injective this

中文:
定理 mk_le_of_module
  结论: (R : 类型u) (E : 类型v)
  证明: by
  obtain ⟨x, hx⟩ : exists (x : E), x != 0 := exists_ne 0
  have : Injective (fun k => k • x) := smul_left_injective R hx
  exact lift_mk_le_lift_mk_of_injective this

Depends on / 依赖: Injective, exists_ne, lift_mk_le_lift_mk_of_injective, smul_left_injective
-/
theorem mk_le_of_module (R : Type u) (E : Type v)
    [AddCommGroup E] [Ring R] [IsDomain R] [Module R E] [Nontrivial E] [Module.IsTorsionFree R E] :
    Cardinal.lift.{v} (#R) <= Cardinal.lift.{u} (#E) := by
  obtain ⟨x, hx⟩ : exists (x : E), x != 0 := exists_ne 0
  have : Injective (fun k => k • x) := smul_left_injective R hx
  exact lift_mk_le_lift_mk_of_injective this

end Cardinal
