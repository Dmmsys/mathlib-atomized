/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Kim Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Ring.Defs

/-!
# Instances on spaces of monoid and group morphisms

This file does two things involving `AddMonoid.End` and `Ring`.
They are separate, and if someone would like to split this file in two that may be helpful.

* We provide the `Ring` structure on `AddMonoid.End`.
* Results about `AddMonoid.End R` when `R` is a ring.
-/

public section


universe uM

variable {M : Type uM}

namespace AddMonoid.End

/-
**AddMonoid.End.instAddMonoidWithOne** 是 Mathlib 中的一个实例，位于命名空间 `AddMonoid.End`。
形式化陈述：instAddMonoidWithOne (M) [AddCommMonoid M] : AddMonoidWithOne (AddMonoid.E
nd M) where natCast n
参数：M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddMonoidWithOne (M) [AddCommMonoid M] : AddMonoidWithOne (AddMonoid.End M) where
  natCast n := n • (1 : AddMonoid.End M)
  natCast_zero := AddMonoid.nsmul_zero _
  natCast_succ n := AddMonoid.nsmul_succ n 1

/-- See also `AddMonoid.End.natCast_def`. -/
@[simp]
/-
**AddMonoid.End.natCast_apply** 是 Mathlib 中的一个引理，位于命名空间 `AddMonoid.End`。
形式化陈述：natCast_apply [AddCommMonoid M] (n : Nat) (m : M) : (↑n : AddMonoid.End M)
 m = n • m
参数：n : Nat；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See also `AddMonoid.End.natCast_def`.
-/
lemma natCast_apply [AddCommMonoid M] (n : ℕ) (m : M) : (↑n : AddMonoid.End M) m = n • m := rfl
/-
**AddMonoid.End.ofNat_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoid.End`。
形式化陈述：∀ {M : Type uM} [inst : AddCommMonoid M] (n : ℕ) [inst_1 : n.AtLeastTwo] (
m : M), (OfNat.ofNat n) m = n • m
参数：n : ℕ；m : M；OfNat.ofNat n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofNat_apply [AddCommMonoid M] (n : ℕ) [n.AtLeastTwo] (m : M) :
    (ofNat(n) : AddMonoid.End M) m = n • m := rfl
/-
**AddMonoid.End.instSemiring** 是 Mathlib 中的一个实例，位于命名空间 `AddMonoid.End`。
形式化陈述：instSemiring [AddCommMonoid M] : Semiring (AddMonoid.End M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemiring [AddCommMonoid M] : Semiring (AddMonoid.End M) :=
  fast_instance% { AddMonoid.End.instMonoid M,
    AddMonoidHom.instAddCommMonoid,
    AddMonoid.End.instAddMonoidWithOne M with
    zero_mul := fun _ => AddMonoidHom.ext fun _ => rfl,
    mul_zero := fun _ => AddMonoidHom.ext fun _ => AddMonoidHom.map_zero _,
    left_distrib := fun _ _ _ => AddMonoidHom.ext fun _ => AddMonoidHom.map_add _ _ _,
    right_distrib := fun _ _ _ => AddMonoidHom.ext fun _ => rfl }
/-
**AddMonoid.End.instRing** 是 Mathlib 中的一个实例，位于命名空间 `AddMonoid.End`。
形式化陈述：instRing [AddCommGroup M] : Ring (AddMonoid.End M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instRing [AddCommGroup M] : Ring (AddMonoid.End M) :=
  fast_instance% { AddMonoid.End.instSemiring, AddMonoid.End.instAddCommGroup with
    intCast := fun z => z • (1 : AddMonoid.End M),
    intCast_ofNat := natCast_zsmul _,
    intCast_negSucc := negSucc_zsmul _ }
/-
**AddMonoid.End.** 是 Mathlib 中的一个示例，位于命名空间 `AddMonoid.End`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [AddCommGroup M] :
    (AddMonoid.End.instRing (M := M)).toAddCommGroup.toAddGroup.toSubNegMonoid =
    (AddMonoid.End.instRing (M := M)).toAddGroupWithOne.toAddGroup.toSubNegMonoid := by
  with_reducible_and_instances rfl

end AddMonoid.End

