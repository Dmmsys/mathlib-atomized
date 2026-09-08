/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.GroupWithZero.Subgroup
public import Mathlib.Algebra.Ring.Submonoid.Pointwise
public import Mathlib.Algebra.Module.Defs

/-!
# Additive subgroups of rings
-/

@[expose] public section

open scoped Pointwise

variable {R M : Type*}

namespace AddSubgroup
section NonUnitalNonAssocRing
variable [NonUnitalNonAssocRing R]

/-- For additive subgroups `S` and `T` of a ring, the product of `S` and `T` as submonoids
is automatically a subgroup, which we define as the product of `S` and `T` as subgroups. -/
@[instance_reducible]
/-
**AddSubgroup.mul** 是 Mathlib 中的一个定义，位于命名空间 `AddSubgroup`。
形式化陈述：{R : Type u_1} → [inst : NonUnitalNonAssocRing R] → Mul (AddSubgroup R)
参数：AddSubgroup R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For additive subgroups `S` and `T` of a ring, the product of `S` and `T` as subm
onoids
is automatically a subgroup, which we define as the product of `S` and `T` as su
bgroups.
-/
protected def mul : Mul (AddSubgroup R) where
  mul M N :=
  { __ := M.toAddSubmonoid * N.toAddSubmonoid
    neg_mem' := fun h ↦ AddSubmonoid.mul_induction_on h
      (fun m hm n hn ↦ by rw [← neg_mul]; exact AddSubmonoid.mul_mem_mul (M.neg_mem hm) hn)
      fun r₁ r₂ h₁ h₂ ↦ by rw [neg_add]; exact (M.1 * N.1).add_mem h₁ h₂ }

scoped[Pointwise] attribute [instance] AddSubgroup.mul
/-
**AddSubgroup.mul_toAddSubmonoid** 是 Mathlib 中的一个引理，位于命名空间 `AddSubgroup`。
形式化陈述：mul_toAddSubmonoid (M N : AddSubgroup R) : (M * N).toAddSubmonoid = M.toAd
dSubmonoid * N.toAddSubmonoid
参数：M N : AddSubgroup R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_toAddSubmonoid (M N : AddSubgroup R) :
    (M * N).toAddSubmonoid = M.toAddSubmonoid * N.toAddSubmonoid := rfl

end NonUnitalNonAssocRing

section Semiring
variable [Semiring R] [AddCommGroup M] [Module R M]

/-
**AddSubgroup.zero_smul** 是 Mathlib 中的一个定理，位于命名空间 `AddSubgroup`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M]   (s : AddSubgroup M), 0 • s = ⊥
参数：s : AddSubgroup M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DistribMulAction.toAddMonoidEnd_apply`：∀ (M : Type u_1) (A : Type u_7) [
inst : Monoid M] [inst_1 : AddMonoid A] [inst_2 : DistribMulAction M A] (x : M),
   (DistribMulAction.toAddM…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `DistribSMul.toAddMonoidHom_apply`：∀ {M : Type u_1} (A : Type u_7) [inst 
: AddZeroClass A] [inst_1 : DistribSMul M A] (x : M) (x_1 : A),   (DistribSMul.t
oAddMonoidHom A x) x_1…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] protected lemma zero_smul (s : AddSubgroup M) : (0 : R) • s = ⊥ := by
  simp [eq_bot_iff_forall, pointwise_smul_def]

end Semiring
end AddSubgroup

