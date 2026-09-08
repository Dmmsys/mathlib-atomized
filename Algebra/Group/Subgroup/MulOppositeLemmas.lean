/-
Copyright (c) 2022 Alex Kontorovich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Subgroup.MulOpposite
public import Mathlib.Algebra.Group.Submonoid.MulOpposite
public import Mathlib.Logic.Encodable.Basic

/-!
# Mul-opposite subgroups

This file contains a somewhat arbitrary assortment of results on the opposite subgroup `H.op`
that rely on further theory to define. As such it is a somewhat arbitrary assortment of results,
which might be organized and split up further.

## Tags
subgroup, subgroups

-/

public section

variable {ι : Sort*} {G : Type*} [Group G]

namespace Subgroup

/-- We redeclare this instance to get keys
`SMul (@Subtype (MulOpposite _) (@Membership.mem (MulOpposite _)
  (Subgroup (MulOpposite _) _) _ (@Subgroup.op _ _ _))) _`
compared to the keys for `Submonoid.smul`
`SMul (@Subtype _ (@Membership.mem _ (Submonoid _ _) _ _)) _` -/
/-
**Subgroup.instSMul** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：{G : Type u_2} → [inst : Group G] → (H : Subgroup G) → SMul (↥H.op) G
参数：H : Subgroup G；↥H.op。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We redeclare this instance to get keys
`SMul (@Subtype (MulOpposite _) (@Membership.mem (MulOpposite _)
  (Subgroup (MulOpposite _) _) _ (@Subgroup.op _ _ _))) _`
compared to the keys for `Submonoid.smul`
`SMul (@Subtype _ (@Membership.mem _ (Submonoid _ _) _ _)) _`
-/
@[to_additive] instance instSMul (H : Subgroup G) : SMul H.op G := Submonoid.smul ..

/-! ### Lattice results -/

@[to_additive (attr := simp)]
/-
**Subgroup.op_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：op_bot : (⊥ : Subgroup G).op = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_bot`：OrderIso.map_bot [LE α] [PartialOrder β] [OrderBot α] 
[OrderBot β] (f : α ≃o β) : f ⊥ = ⊥

--- 原说明 ---
### Lattice results
-/
theorem op_bot : (⊥ : Subgroup G).op = ⊥ := opEquiv.map_bot

@[to_additive (attr := simp)]
/-
**Subgroup.op_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：op_eq_bot {S : Subgroup G} : S.op = ⊥ ↔ S = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Subgroup.op_injective`：op_injective : (@Subgroup.op G _).Injective
· 使用定理 `Subgroup.op_bot`：op_bot : (⊥ : Subgroup G).op = ⊥
-/
theorem op_eq_bot {S : Subgroup G} : S.op = ⊥ ↔ S = ⊥ := op_injective.eq_iff' op_bot

@[to_additive (attr := simp)]
/-
**Subgroup.unop_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：unop_bot : (⊥ : Subgroup Gᵐᵒᵖ).unop = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_bot`：OrderIso.map_bot [LE α] [PartialOrder β] [OrderBot α] 
[OrderBot β] (f : α ≃o β) : f ⊥ = ⊥
-/
theorem unop_bot : (⊥ : Subgroup Gᵐᵒᵖ).unop = ⊥ := opEquiv.symm.map_bot

@[to_additive (attr := simp)]
/-
**Subgroup.unop_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：unop_eq_bot {S : Subgroup Gᵐᵒᵖ} : S.unop = ⊥ ↔ S = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Subgroup.unop_injective`：unop_injective : (@Subgroup.unop G _).Injective
· 使用定理 `Subgroup.unop_bot`：unop_bot : (⊥ : Subgroup Gᵐᵒᵖ).unop = ⊥
-/
theorem unop_eq_bot {S : Subgroup Gᵐᵒᵖ} : S.unop = ⊥ ↔ S = ⊥ := unop_injective.eq_iff' unop_bot

@[to_additive (attr := simp)]
/-
**Subgroup.op_top** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：op_top : (⊤ : Subgroup G).op = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_top : (⊤ : Subgroup G).op = ⊤ := rfl

@[to_additive (attr := simp)]
/-
**Subgroup.op_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：op_eq_top {S : Subgroup G} : S.op = ⊤ ↔ S = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Subgroup.op_injective`：op_injective : (@Subgroup.op G _).Injective
· 使用定理 `Subgroup.op_top`：op_top : (⊤ : Subgroup G).op = ⊤
-/
theorem op_eq_top {S : Subgroup G} : S.op = ⊤ ↔ S = ⊤ := op_injective.eq_iff' op_top

@[to_additive (attr := simp)]
/-
**Subgroup.unop_top** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：unop_top : (⊤ : Subgroup Gᵐᵒᵖ).unop = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_top : (⊤ : Subgroup Gᵐᵒᵖ).unop = ⊤ := rfl

@[to_additive (attr := simp)]
/-
**Subgroup.unop_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：unop_eq_top {S : Subgroup Gᵐᵒᵖ} : S.unop = ⊤ ↔ S = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Subgroup.unop_injective`：unop_injective : (@Subgroup.unop G _).Injective
· 使用定理 `Subgroup.unop_top`：unop_top : (⊤ : Subgroup Gᵐᵒᵖ).unop = ⊤
-/
theorem unop_eq_top {S : Subgroup Gᵐᵒᵖ} : S.unop = ⊤ ↔ S = ⊤ := unop_injective.eq_iff' unop_top

@[to_additive]
/-
**Subgroup.op_sup** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：op_sup (S₁ S₂ : Subgroup G) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op
参数：S₁ S₂ : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] [inst_1 : SemilatticeSup β] (f : α ≃o β) (x y : α),   f (x ⊔ y) = f x ⊔ f y
-/
theorem op_sup (S₁ S₂ : Subgroup G) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op :=
  opEquiv.map_sup _ _

@[to_additive]
/-
**Subgroup.unop_sup** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：unop_sup (S₁ S₂ : Subgroup Gᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop
参数：S₁ S₂ : Subgroup Gᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] [inst_1 : SemilatticeSup β] (f : α ≃o β) (x y : α),   f (x ⊔ y) = f x ⊔ f y
-/
theorem unop_sup (S₁ S₂ : Subgroup Gᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop :=
  opEquiv.symm.map_sup _ _

@[to_additive]
/-
**Subgroup.op_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：op_inf (S₁ S₂ : Subgroup G) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op
参数：S₁ S₂ : Subgroup G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_inf (S₁ S₂ : Subgroup G) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op := rfl

@[to_additive]
/-
**Subgroup.unop_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：unop_inf (S₁ S₂ : Subgroup Gᵐᵒᵖ) : (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop
参数：S₁ S₂ : Subgroup Gᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_inf (S₁ S₂ : Subgroup Gᵐᵒᵖ) : (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop := rfl

@[to_additive]
/-
**Subgroup.op_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：op_sSup (S : Set (Subgroup G)) : (sSup S).op = sSup (.unop ⁻¹' S)
参数：S : Set (Subgroup G)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sSup_eq_sSup_symm_preimage`：OrderIso.map_sSup_eq_sSup_symm_
preimage [CompleteLattice β] (f : α ≃o β) (s : Set α) : f (sSup s) = sSup (f.sym
m ⁻¹' s)
-/
theorem op_sSup (S : Set (Subgroup G)) : (sSup S).op = sSup (.unop ⁻¹' S) :=
  opEquiv.map_sSup_eq_sSup_symm_preimage _

@[to_additive]
/-
**Subgroup.unop_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：unop_sSup (S : Set (Subgroup Gᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S)
参数：S : Set (Subgroup Gᵐᵒᵖ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sSup_eq_sSup_symm_preimage`：OrderIso.map_sSup_eq_sSup_symm_
preimage [CompleteLattice β] (f : α ≃o β) (s : Set α) : f (sSup s) = sSup (f.sym
m ⁻¹' s)
-/
theorem unop_sSup (S : Set (Subgroup Gᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) :=
  opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

@[to_additive]
/-
**Subgroup.op_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：op_sInf (S : Set (Subgroup G)) : (sInf S).op = sInf (.unop ⁻¹' S)
参数：S : Set (Subgroup G)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sInf_eq_sInf_symm_preimage`：∀ {α : Type u_1} {β : Type u_2}
 [inst : CompleteLattice α] [inst_1 : CompleteLattice β] (f : α ≃o β) (s : Set α
),   f (sInf s) = sInf (⇑f.sy…
-/
theorem op_sInf (S : Set (Subgroup G)) : (sInf S).op = sInf (.unop ⁻¹' S) :=
  opEquiv.map_sInf_eq_sInf_symm_preimage _

@[to_additive]
/-
**Subgroup.unop_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：unop_sInf (S : Set (Subgroup Gᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S)
参数：S : Set (Subgroup Gᵐᵒᵖ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sInf_eq_sInf_symm_preimage`：∀ {α : Type u_1} {β : Type u_2}
 [inst : CompleteLattice α] [inst_1 : CompleteLattice β] (f : α ≃o β) (s : Set α
),   f (sInf s) = sInf (⇑f.sy…
-/
theorem unop_sInf (S : Set (Subgroup Gᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) :=
  opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

@[to_additive]
/-
**Subgroup.op_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：op_iSup (S : ι -> Subgroup G) : (iSup S).op = ⨆ i, (S i).op
参数：S : ι -> Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_iSup`：OrderIso.map_iSup [CompleteLattice β] (f : α ≃o β) (x
 : ι -> α) : f (⨆ i, x i) = ⨆ i, f (x i)
-/
theorem op_iSup (S : ι → Subgroup G) : (iSup S).op = ⨆ i, (S i).op := opEquiv.map_iSup _

@[to_additive]
/-
**Subgroup.unop_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：unop_iSup (S : ι -> Subgroup Gᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop
参数：S : ι -> Subgroup Gᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_iSup`：OrderIso.map_iSup [CompleteLattice β] (f : α ≃o β) (x
 : ι -> α) : f (⨆ i, x i) = ⨆ i, f (x i)
-/
theorem unop_iSup (S : ι → Subgroup Gᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop :=
  opEquiv.symm.map_iSup _

@[to_additive]
/-
**Subgroup.op_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：op_iInf (S : ι -> Subgroup G) : (iInf S).op = ⨅ i, (S i).op
参数：S : ι -> Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_iInf`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] (f : α ≃o β)   (x : ι → α), f 
(⨅ i, x…
-/
theorem op_iInf (S : ι → Subgroup G) : (iInf S).op = ⨅ i, (S i).op := opEquiv.map_iInf _

@[to_additive]
/-
**Subgroup.unop_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：unop_iInf (S : ι -> Subgroup Gᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop
参数：S : ι -> Subgroup Gᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_iInf`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] (f : α ≃o β)   (x : ι → α), f 
(⨅ i, x…
-/
theorem unop_iInf (S : ι → Subgroup Gᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop :=
  opEquiv.symm.map_iInf _

@[to_additive]
/-
**Subgroup.op_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：op_closure (s : Set G) : (closure s).op = closure (MulOpposite.unop ⁻¹' s)
参数：s : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.op_sInf`：op_sInf (S : Set (Subgroup G)) : (sInf S).op = sInf (.
unop ⁻¹' S)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subgroup.coe_unop`：∀ {G : Type u_2} [inst : Group G] (H : Subgroup Gᵐᵒᵖ)
, ↑H.unop = MulOpposite.op ⁻¹' ↑H
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `MulOpposite.unop_surjective`：unop_surjective : Surjective (unop : αᵐᵒᵖ -
> α)
-/
theorem op_closure (s : Set G) : (closure s).op = closure (MulOpposite.unop ⁻¹' s) := by
  simp_rw [closure, op_sInf, Set.preimage_ofPred_eq, Subgroup.coe_unop]
  congr with a
  exact MulOpposite.unop_surjective.forall

@[to_additive]
/-
**Subgroup.unop_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：unop_closure (s : Set Gᵐᵒᵖ) : (closure s).unop = closure (MulOpposite.op ⁻
¹' s)
参数：s : Set Gᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.op_inj`：op_inj {S T : Subgroup G} : S.op = T.op ↔ S = T
· 使用定理 `Subgroup.op_unop`：op_unop (S : Subgroup Gᵐᵒᵖ) : S.unop.op = S
· 使用定理 `Subgroup.op_closure`：op_closure (s : Set G) : (closure s).op = closure (
MulOpposite.unop ⁻¹' s)
· 使用定理 `Set.preimage_preimage`：preimage_preimage {g : β -> γ} {f : α -> β} {s : 
Set γ} : f ⁻¹' g ⁻¹' s = (fun x => g (f x)) ⁻¹' s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem unop_closure (s : Set Gᵐᵒᵖ) : (closure s).unop = closure (MulOpposite.op ⁻¹' s) := by
  rw [← op_inj, op_unop, op_closure]
  simp_rw [Set.preimage_preimage, MulOpposite.op_unop, Set.preimage_id']

@[to_additive]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (H : Subgroup G) [Encodable H] : Encodable H.op :=
  Encodable.ofEquiv H H.equivOp.symm

@[to_additive]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (H : Subgroup G) [Countable H] : Countable H.op :=
  Countable.of_equiv H H.equivOp

@[to_additive]
/-
**Subgroup.smul_opposite_mul** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：smul_opposite_mul {H : Subgroup G} (x g : G) (h : H.op) : h • (g * x) = g 
* h • x
参数：x g : G；h : H.op。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem smul_opposite_mul {H : Subgroup G} (x g : G) (h : H.op) :
    h • (g * x) = g * h • x :=
  mul_assoc _ _ _

@[to_additive (attr := simp)]
/-
**Subgroup.normal_op** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normal_op {H : Subgroup G} : H.op.Normal ↔ H.Normal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem normal_op {H : Subgroup G} : H.op.Normal ↔ H.Normal := by
  simp only [← normalizer_eq_top_iff, ← op_normalizer, op_eq_top]

@[to_additive] alias ⟨Normal.of_op, Normal.op⟩ := normal_op

@[to_additive]
/-
**Subgroup.op.instNormal** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.op`。
形式化陈述：∀ {G : Type u_2} [inst : Group G] {H : Subgroup G} [H.Normal], H.op.Normal
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.Normal.op`：∀ {G : Type u_2} [inst : Group G] {H : Subgroup G}, 
H.Normal → H.op.Normal
-/
instance op.instNormal {H : Subgroup G} [H.Normal] : H.op.Normal := .op ‹_›

@[to_additive (attr := simp)]
/-
**Subgroup.normal_unop** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normal_unop {H : Subgroup Gᵐᵒᵖ} : H.unop.Normal ↔ H.Normal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.normal_op`：normal_op {H : Subgroup G} : H.op.Normal ↔ H.Normal
· 使用定理 `Subgroup.op_unop`：op_unop (S : Subgroup Gᵐᵒᵖ) : S.unop.op = S
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem normal_unop {H : Subgroup Gᵐᵒᵖ} : H.unop.Normal ↔ H.Normal := by
  rw [← normal_op, op_unop]

@[to_additive] alias ⟨Normal.of_unop, Normal.unop⟩ := normal_unop

@[to_additive]
/-
**Subgroup.unop.instNormal** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.unop`。
形式化陈述：∀ {G : Type u_2} [inst : Group G] {H : Subgroup Gᵐᵒᵖ} [H.Normal], H.unop.N
ormal
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.Normal.unop`：∀ {G : Type u_2} [inst : Group G] {H : Subgroup Gᵐ
ᵒᵖ}, H.Normal → H.unop.Normal
-/
instance unop.instNormal {H : Subgroup Gᵐᵒᵖ} [H.Normal] : H.unop.Normal := .unop ‹_›

end Subgroup

