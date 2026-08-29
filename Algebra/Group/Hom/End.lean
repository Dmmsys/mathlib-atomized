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

/--
Instance `instAddMonoidWithOne` / 实例 `instAddMonoidWithOne`

English:
instance instAddMonoidWithOne
  signature: (M) [AddCommMonoid M]
  body: n • (1 : AddMonoid.End M)
  natCast_zero := AddMonoid.nsmul_zero _
  natCast_succ n := AddMonoid.nsmul_succ n 1

中文:
实例 instAddMonoidWithOne
  签名: (M) [加法交换幺半群 M]
  定义体: n • (1 : AddMonoid.End M)
  natCast_zero := AddMonoid.nsmul_zero _
  natCast_succ n := AddMonoid.nsmul_succ n 1

Depends on / 依赖: AddMonoid, AddMonoid.End
-/
instance instAddMonoidWithOne (M) [AddCommMonoid M] : AddMonoidWithOne (AddMonoid.End M) where
  natCast n := n • (1 : AddMonoid.End M)
  natCast_zero := AddMonoid.nsmul_zero _
  natCast_succ n := AddMonoid.nsmul_succ n 1

/-- See also `AddMonoid.End.natCast_def`. -/
@[simp]
/--
lemma `natCast_apply` / 引理 `natCast_apply`

English:
lemma natCast_apply
  given: [AddCommMonoid M] (n : Nat) (m : M)
  statement: (↑n : AddMonoid.End M) m = n • m
  proof: rfl

中文:
引理 natCast_apply
  条件: [加法交换幺半群 M] (n : 自然数) (m : M)
  结论: (↑n : 加法幺半群.End M) m = n • m
  证明: rfl
-/
lemma natCast_apply [AddCommMonoid M] (n : Nat) (m : M) : (↑n : AddMonoid.End M) m = n • m := rfl

/--
lemma `ofNat_apply` / 引理 `ofNat_apply`

English:
lemma ofNat_apply
  given: [AddCommMonoid M] (n : Nat) [n.AtLeastTwo] (m : M)
  proof: rfl

中文:
引理 of自然数_apply
  条件: [加法交换幺半群 M] (n : 自然数) [n.AtLeastTwo] (m : M)
  证明: rfl
-/
@[simp] lemma ofNat_apply [AddCommMonoid M] (n : Nat) [n.AtLeastTwo] (m : M) :
    (ofNat(n) : AddMonoid.End M) m = n • m := rfl

/--
Instance `instSemiring` / 实例 `instSemiring`

English:
instance instSemiring
  signature: [AddCommMonoid M]
  body: fast_instance% { AddMonoid.End.instMonoid M,
    AddMonoidHom.instAddCommMonoid,
    AddMonoid.End.instAddMonoidWithOne M with
    zero_mul := fun _ => AddMonoidHom.ext fun _ => rfl,
    mul_zero := fun _ => AddMonoidHom.ext fun _ => AddMonoidHom.map_zero _,
    left_distrib := fun _ _ _ => AddMonoi

中文:
实例 instSemiring
  签名: [加法交换幺半群 M]
  定义体: fast_instance% { AddMonoid.End.instMonoid M,
    AddMonoidHom.instAddCommMonoid,
    AddMonoid.End.instAddMonoidWithOne M with
    zero_mul := fun _ => AddMonoidHom.ext fun _ => rfl,
    mul_zero := fun _ => AddMonoidHom.ext fun _ => AddMonoidHom.map_zero _,
    left_distrib := fun _ _ _ => AddMonoi

Depends on / 依赖: AddMonoid, AddMonoid.End.instAddMonoidWithOne, AddMonoid.End.instMonoid, AddMonoidHom, AddMonoidHom.ext, AddMonoidHom.instAddCommMonoid, AddMonoidHom.map_add, AddMonoidHom.map_zero, fast_instance, instAddCommMonoid, instAddMonoidWithOne, instMonoid, left_distrib, map_add, map_zero, mul_zero, right_distrib, zero_mul
-/
instance instSemiring [AddCommMonoid M] : Semiring (AddMonoid.End M) :=
  fast_instance% { AddMonoid.End.instMonoid M,
    AddMonoidHom.instAddCommMonoid,
    AddMonoid.End.instAddMonoidWithOne M with
    zero_mul := fun _ => AddMonoidHom.ext fun _ => rfl,
    mul_zero := fun _ => AddMonoidHom.ext fun _ => AddMonoidHom.map_zero _,
    left_distrib := fun _ _ _ => AddMonoidHom.ext fun _ => AddMonoidHom.map_add _ _ _,
    right_distrib := fun _ _ _ => AddMonoidHom.ext fun _ => rfl }

/--
Instance `instRing` / 实例 `instRing`

English:
instance instRing
  signature: [AddCommGroup M]
  body: fast_instance% { AddMonoid.End.instSemiring, AddMonoid.End.instAddCommGroup with
    intCast := fun z => z • (1 : AddMonoid.End M),
    intCast_ofNat := natCast_zsmul _,
    intCast_negSucc := negSucc_zsmul _ }

example [AddCommGroup M] :
    (AddMonoid.End.instRing (M := M)).toAddCommGroup.toAddGro

中文:
实例 instRing
  签名: [加法交换群 M]
  定义体: fast_instance% { AddMonoid.End.instSemiring, AddMonoid.End.instAddCommGroup with
    intCast := fun z => z • (1 : AddMonoid.End M),
    intCast_ofNat := natCast_zsmul _,
    intCast_negSucc := negSucc_zsmul _ }

example [AddCommGroup M] :
    (AddMonoid.End.instRing (M := M)).toAddCommGroup.toAddGro

Depends on / 依赖: AddMonoid, AddMonoid.End, AddMonoid.End.instAddCommGroup, AddMonoid.End.instSemiring, fast_instance, instAddCommGroup, instSemiring, intCast, intCast_negSucc, intCast_ofNat, natCast_zsmul, negSucc_zsmul
-/
instance instRing [AddCommGroup M] : Ring (AddMonoid.End M) :=
  fast_instance% { AddMonoid.End.instSemiring, AddMonoid.End.instAddCommGroup with
    intCast := fun z => z • (1 : AddMonoid.End M),
    intCast_ofNat := natCast_zsmul _,
    intCast_negSucc := negSucc_zsmul _ }

example [AddCommGroup M] :
    (AddMonoid.End.instRing (M := M)).toAddCommGroup.toAddGroup.toSubNegMonoid =
    (AddMonoid.End.instRing (M := M)).toAddGroupWithOne.toAddGroup.toSubNegMonoid := by
  with_reducible_and_instances rfl

end AddMonoid.End
