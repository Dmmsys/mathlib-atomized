/-
Copyright (c) 2018 Kevin Buzzard, Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Patrick Massot
-/
-- This file is to a certain extent based on `quotient_module.lean` by Johannes Hölzl.
module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.Finite.Prod
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Deducing finiteness of a group.
-/

@[expose] public section

open Function QuotientGroup Subgroup
open scoped Pointwise


variable {F G H : Type*} [Group F] [Group G] [Group H] [Fintype F] [Fintype H]
variable (f : F →* G) (g : G →* H)

namespace Group

open scoped Classical in
/-- If `F` and `H` are finite such that `ker(G →* H) ≤ im(F →* G)`, then `G` is finite. -/
@[to_additive (attr := instance_reducible)
/-- If `F` and `H` are finite such that `ker(G →+ H) ≤ im(F →+ G)`, then `G` is finite. -/]
/-
**Group.fintypeOfKerLeRange** 是 Mathlib 中的一个定义，位于命名空间 `Group`。
形式化陈述：fintypeOfKerLeRange (h : g.ker <= f.range) : Fintype G
参数：h : g.ker <= f.range。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientGroup.kerLift_injective`：kerLift_injective : Injective (kerLift 
φ)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
noncomputable def fintypeOfKerLeRange (h : g.ker ≤ f.range) : Fintype G :=
  @Fintype.ofEquiv _ _
    (@instFintypeProd _ _ (Fintype.ofInjective _ <| kerLift_injective g) <|
      Fintype.ofInjective _ <| inclusion_injective h)
    groupEquivQuotientProdSubgroup.symm

/-- If `F` and `H` are finite such that `ker(G →* H) = im(F →* G)`, then `G` is finite. -/
@[to_additive (attr := instance_reducible)
/-- If `F` and `H` are finite such that `ker(G →+ H) = im(F →+ G)`, then `G` is finite. -/]
/-
**Group.fintypeOfKerEqRange** 是 Mathlib 中的一个定义，位于命名空间 `Group`。
形式化陈述：fintypeOfKerEqRange (h : g.ker = f.range) : Fintype G
参数：h : g.ker = f.range。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def fintypeOfKerEqRange (h : g.ker = f.range) : Fintype G :=
  fintypeOfKerLeRange _ _ h.le

/-- If `ker(G →* H)` and `H` are finite, then `G` is finite. -/
@[to_additive (attr := instance_reducible)
  /-- If `ker(G →+ H)` and `H` are finite, then `G` is finite. -/]
/-
**Group.fintypeOfKerOfCodom** 是 Mathlib 中的一个定义，位于命名空间 `Group`。
形式化陈述：fintypeOfKerOfCodom [Fintype g.ker] : Fintype G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def fintypeOfKerOfCodom [Fintype g.ker] : Fintype G :=
  fintypeOfKerLeRange ((topEquiv : _ ≃* G).toMonoidHom.comp <| inclusion le_top) g fun x hx =>
    ⟨⟨x, hx⟩, rfl⟩

/-- If `F` and `coker(F →* G)` are finite, then `G` is finite. -/
@[to_additive (attr := instance_reducible)
  /-- If `F` and `coker(F →+ G)` are finite, then `G` is finite. -/]
/-
**Group.fintypeOfDomOfCoker** 是 Mathlib 中的一个定义，位于命名空间 `Group`。
形式化陈述：fintypeOfDomOfCoker [Normal f.range] [Fintype <| G ⧸ f.range] : Fintype G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def fintypeOfDomOfCoker [Normal f.range] [Fintype <| G ⧸ f.range] : Fintype G :=
  fintypeOfKerLeRange _ (mk' f.range) fun x => (eq_one_iff x).mp

end Group

@[to_additive]
/-
**finite_iff_subgroup_quotient** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finite_iff_subgroup_quotient (H : Subgroup G) : Finite G ↔ Finite H ∧ Fini
te (G ⧸ H)
参数：H : Subgroup G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.finite_iff`：Equiv.finite_iff (f : α ≃ β) : Finite α ↔ Finite β
· 使用引理 `Prod.finite_iff`：Prod.finite_iff [Nonempty α] [Nonempty β] : Finite (α ×
 β) ↔ Finite α ∧ Finite β where mp _
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma finite_iff_subgroup_quotient (H : Subgroup G) : Finite G ↔ Finite H ∧ Finite (G ⧸ H) := by
  rw [(groupEquivQuotientProdSubgroup (s := H)).finite_iff, Prod.finite_iff, and_comm]

@[to_additive]
/-
**Finite.of_subgroup_quotient** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finite.of_subgroup_quotient (H : Subgroup G) [Finite H] [Finite (G ⧸ H)] :
 Finite G
参数：H : Subgroup G；G ⧸ H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `finite_iff_subgroup_quotient`：finite_iff_subgroup_quotient (H : Subgroup
 G) : Finite G ↔ Finite H ∧ Finite (G ⧸ H)
-/
lemma Finite.of_subgroup_quotient (H : Subgroup G) [Finite H] [Finite (G ⧸ H)] : Finite G := by
  rw [finite_iff_subgroup_quotient]; constructor <;> assumption
