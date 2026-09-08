/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.Algebra.Module.NatInt

/-!
# Module structure and endomorphisms

In this file, we define `Module.toAddMonoidEnd`, which is `(•)` as a monoid homomorphism.
We use this to prove some results on scalar multiplication by integers.
-/

@[expose] public section

assert_not_exists RelIso Multiset Set.indicator Pi.single_smul₀ Field

open Function Set

universe u v

variable {R S M M₂ : Type*}

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M] (r s : R) (x : M)

/-
**AddMonoid.End.natCast_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddMonoid.End.natCast_def (n : Nat) : (↑n : AddMonoid.End M) = DistribMulA
ction.toAddMonoidEnd Nat M n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AddMonoid.End.natCast_def (n : ℕ) :
    (↑n : AddMonoid.End M) = DistribMulAction.toAddMonoidEnd ℕ M n :=
  rfl

variable (R M)

set_option backward.isDefEq.respectTransparency false in
/-- `(•)` as an `AddMonoidHom`.

This is a stronger version of `DistribMulAction.toAddMonoidEnd` -/
@[simps! apply_apply]
/-
**Module.toAddMonoidEnd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Module.toAddMonoidEnd : R ->+* AddMonoid.End M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`(•)` as an `AddMonoidHom`.

This is a stronger version of `DistribMulAction.toAddMonoidEnd`
-/
def Module.toAddMonoidEnd : R →+* AddMonoid.End M :=
  { DistribMulAction.toAddMonoidEnd R M with
    map_zero' := AddMonoidHom.ext fun r => by simp
    map_add' x y :=
      AddMonoidHom.ext fun r => by simp [(AddMonoidHom.add_apply), add_smul] }

/-- A convenience alias for `Module.toAddMonoidEnd` as an `AddMonoidHom`, usually to allow the
use of `AddMonoidHom.flip`. -/
/-
**smulAddHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：smulAddHom : R ->+ M ->+ M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A convenience alias for `Module.toAddMonoidEnd` as an `AddMonoidHom`, usually to
 allow the
use of `AddMonoidHom.flip`.
-/
def smulAddHom : R →+ M →+ M :=
  (Module.toAddMonoidEnd R M).toAddMonoidHom

variable {R M}

@[simp]
/-
**smulAddHom_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smulAddHom_apply : smulAddHom R M r x = r • x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smulAddHom_apply : smulAddHom R M r x = r • x :=
  rfl

variable {x}
/-
**IsAddUnit.smul_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAddUnit.smul_left [DistribSMul S M] (hx : IsAddUnit x) (s : S) : IsAddUn
it (s • x)
参数：hx : IsAddUnit x；s : S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAddUnit.map`：∀ {F : Type u_1} {M : Type u_3} {N : Type u_4} [inst : Fu
nLike F M N] [inst_1 : AddMonoid M] [inst_2 : AddMonoid N]   [AddMonoidHomClass 
F M…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
lemma IsAddUnit.smul_left [DistribSMul S M] (hx : IsAddUnit x) (s : S) :
    IsAddUnit (s • x) :=
  hx.map (DistribSMul.toAddMonoidHom M s)

variable {r} (x)
/-
**IsAddUnit.smul_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAddUnit.smul_right (hr : IsAddUnit r) : IsAddUnit (r • x)
参数：hr : IsAddUnit r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAddUnit.map`：∀ {F : Type u_1} {M : Type u_3} {N : Type u_4} [inst : Fu
nLike F M N] [inst_1 : AddMonoid M] [inst_2 : AddMonoid N]   [AddMonoidHomClass 
F M…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
lemma IsAddUnit.smul_right (hr : IsAddUnit r) : IsAddUnit (r • x) :=
  hr.map (AddMonoidHom.flip (smulAddHom R M) x)

end AddCommMonoid

section AddCommGroup

variable (R M) [Semiring R] [AddCommGroup M]

/-
**AddMonoid.End.intCast_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddMonoid.End.intCast_def (z : Int) : (↑z : AddMonoid.End M) = DistribMulA
ction.toAddMonoidEnd Int M z
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AddMonoid.End.intCast_def (z : ℤ) :
    (↑z : AddMonoid.End M) = DistribMulAction.toAddMonoidEnd ℤ M z :=
  rfl

end AddCommGroup

