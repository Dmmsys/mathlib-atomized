/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# MulAction and MulDistribMulAction of quotient group on fixed points

Given a `MulAction`/`MulDistribMulAction` of a group `G` on `A` and a normal subgroup `H` of `G`,
there is a `MulAction`/`MulDistribMulAction` of the quotient group `G ⧸ H` on `fixedPoints H A`.

-/

public section

namespace MulAction

variable {G : Type*} [Group G] {A : Type*} [MulAction G A]

variable {H : Subgroup G} [H.Normal]

/-
**MulAction.** 是 Mathlib 中的一个实例，位于命名空间 `MulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction (G ⧸ H) (fixedPoints H A) :=
  ofEndHom <|
    QuotientGroup.lift H (toEndHom : G →* Function.End (fixedPoints H A))
    (fun g hg ↦ by funext a; ext; exact a.2 ⟨g, hg⟩)

@[simp]
/-
**MulAction.coe_quotient_smul_fixedPoints** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：coe_quotient_smul_fixedPoints (g : G) (a : fixedPoints H A) : (g : G ⧸ H) 
• a = g • a
参数：g : G；a : fixedPoints H A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_quotient_smul_fixedPoints (g : G) (a : fixedPoints H A) :
    (g : G ⧸ H) • a = g • a := rfl

@[simp]
/-
**MulAction.quotient_out_smul_fixedPoints** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：quotient_out_smul_fixedPoints (g : G ⧸ H) (a : fixedPoints H A) : g.out • 
a = g • a
参数：g : G ⧸ H；a : fixedPoints H A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quotient.out_eq`：Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.ou
t⟧ = q
-/
lemma quotient_out_smul_fixedPoints (g : G ⧸ H) (a : fixedPoints H A) :
    g.out • a = g • a := by
  conv_rhs => rw [← g.out_eq]
  rfl

end MulAction

namespace MulDistribMulAction

open MulAction

variable {G : Type*} [Group G] {A : Type*} [Monoid A] [MulDistribMulAction G A]

variable {H : Subgroup G} [H.Normal]

/-
**MulDistribMulAction.** 是 Mathlib 中的一个实例，位于命名空间 `MulDistribMulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulDistribMulAction (G ⧸ H) (FixedPoints.submonoid H A) where
  __ := (inferInstance : MulAction (G ⧸ H) (fixedPoints H A))
  smul_mul g a b := g.induction_on fun g ↦ Subtype.ext (smul_mul g a.1 b.1)
  smul_one g := g.induction_on fun g ↦ Subtype.ext (smul_one g)

open scoped FixedPoints

variable {α : Type*} [Group α] [MulDistribMulAction G α]
/-
**MulDistribMulAction.** 是 Mathlib 中的一个实例，位于命名空间 `MulDistribMulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulDistribMulAction (G ⧸ H) (FixedPoints.subgroup H α) :=
  inferInstanceAs <| MulDistribMulAction (G ⧸ H) (FixedPoints.submonoid H α)

end MulDistribMulAction

