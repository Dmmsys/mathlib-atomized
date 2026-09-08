/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Saturated subgroups

## Tags
subgroup, subgroups

-/

@[expose] public section


namespace Submonoid

variable {G : Type*} [Monoid G]

/-- A submonoid `H` of `G` is *saturated* if for all `n : ℕ` and `g : G` with `g^n ∈ H` we have
`n = 0` or `g ∈ H`. We use the name `PowSaturated` to distinguish from `Submonoid.MulSaturated`. -/
@[to_additive
/-- An additive submonoid `H` of `G` is *saturated* if for all `n : ℕ` and `g : G` with
`n•g ∈ H` we have `n = 0` or `g ∈ H`. We use the name `NSMulSaturated` to distinguish from
`Submonoid.MulSaturated`. -/]
/-
**Submonoid.PowSaturated** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：PowSaturated (H : Submonoid G) : Prop
参数：H : Submonoid G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def PowSaturated (H : Submonoid G) : Prop :=
  ∀ ⦃n g⦄, g ^ n ∈ H → n = 0 ∨ g ∈ H

@[to_additive]
/-
**Submonoid.powSaturated_iff_npow** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：powSaturated_iff_npow {H : Submonoid G} : PowSaturated H ↔ forall (n : Nat
) (g : G), g ^ n in H -> n = 0 ∨ g in H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem powSaturated_iff_npow {H : Submonoid G} :
    PowSaturated H ↔ ∀ (n : ℕ) (g : G), g ^ n ∈ H → n = 0 ∨ g ∈ H :=
  Iff.rfl

end Submonoid

@[deprecated (since := "2026-03-03")] alias Subgroup.Saturated := Submonoid.PowSaturated
@[deprecated (since := "2026-03-03")] alias AddSubgroup.Saturated := AddSubmonoid.NSMulSaturated
@[deprecated (since := "2026-03-03")]
alias Subgroup.saturated_iff_npow := Submonoid.powSaturated_iff_npow
@[deprecated (since := "2026-03-03")]
alias AddSubgroup.saturated_iff_nsmul := AddSubmonoid.nsmulSaturated_iff_nsmul

namespace Subgroup

variable {G : Type*} [Group G]

@[to_additive]
/-
**Subgroup.saturated_iff_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：saturated_iff_zpow {H : Subgroup G} : H.PowSaturated ↔ forall (n : Int) (g
 : G), g ^ n in H -> n = 0 ∨ g in H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.eq_nat_or_neg`：∀ (a : ℤ), ∃ n, a = ↑n ∨ a = -↑n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
theorem saturated_iff_zpow {H : Subgroup G} :
    H.PowSaturated ↔ ∀ (n : ℤ) (g : G), g ^ n ∈ H → n = 0 ∨ g ∈ H := by
  refine ⟨fun h n g hgn ↦ ?_, fun h n g hgn ↦ by simpa using h n g (by simpa using hgn)⟩
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg <;> simpa using h (by simpa using hgn)

end Subgroup

namespace AddSubmonoid

/-
**AddSubmonoid.ker_saturated** 是 Mathlib 中的一个定理，位于命名空间 `AddSubmonoid`。
形式化陈述：ker_saturated {A₁ A₂ : Type*} [AddGroup A₁] [AddMonoid A₂] [IsAddTorsionFr
ee A₂] (f : A₁ ->+ A₂) : f.ker.NSMulSaturated
参数：f : A₁ ->+ A₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_nsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddMonoid G] [inst_2 : AddMonoid H]   [AddMonoidHomClass F G…
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem ker_saturated {A₁ A₂ : Type*} [AddGroup A₁] [AddMonoid A₂] [IsAddTorsionFree A₂]
    (f : A₁ →+ A₂) : f.ker.NSMulSaturated := by simp [NSMulSaturated, or_comm]

end AddSubmonoid

@[deprecated (since := "2026-03-03")] alias AddSubgroup.ker_saturated := AddSubmonoid.ker_saturated

