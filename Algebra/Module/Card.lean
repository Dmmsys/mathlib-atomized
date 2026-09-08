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

/-- The cardinality of a nontrivial torsion-free module over a domain is at least the cardinality of
the ring. -/
/-
**Cardinal.mk_le_of_module** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_le_of_module (R : Type u) (E : Type v) [AddCommGroup E] [Ring R] [IsDom
ain R] [Module R E] [Nontrivial E] [Module.IsTorsionFree R E] : Cardinal.lift.{v
} (#R) <= Cardinal.lift.{u} (#E)
参数：R : Type u；E : Type v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用引理 `smul_left_injective`：smul_left_injective (hm : m != 0) : ((· • m) : R ->
 M).Injective
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `Cardinal.lift_mk_le_lift_mk_of_injective`：lift_mk_le_lift_mk_of_injectiv
e {α : Type u} {β : Type v} {f : α -> β} (hf : Injective f) : Cardinal.lift.{v} 
(#α) <= Cardinal.lift.{u} (#β)

--- 原说明 ---
The cardinality of a nontrivial torsion-free module over a domain is at least th
e cardinality of
the ring.
-/
theorem mk_le_of_module (R : Type u) (E : Type v)
    [AddCommGroup E] [Ring R] [IsDomain R] [Module R E] [Nontrivial E] [Module.IsTorsionFree R E] :
    Cardinal.lift.{v} (#R) ≤ Cardinal.lift.{u} (#E) := by
  obtain ⟨x, hx⟩ : ∃ (x : E), x ≠ 0 := exists_ne 0
  have : Injective (fun k ↦ k • x) := smul_left_injective R hx
  exact lift_mk_le_lift_mk_of_injective this

end Cardinal

