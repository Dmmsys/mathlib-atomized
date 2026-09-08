/-
Copyright (c) 2025 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/
module

public import Mathlib.Algebra.Group.Subsemigroup.Basic
public import Mathlib.Algebra.Opposites

/-!
# Subsemigroup of opposite semigroups

For every semigroup `M`, we construct an equivalence between subsemigroups of `M` and that of
`Mᵐᵒᵖ`.

-/

@[expose] public section

assert_not_exists MonoidWithZero

variable {ι : Sort*} {M : Type*} [Mul M]

namespace Subsemigroup

/-- Pull a subsemigroup back to an opposite subsemigroup along `MulOpposite.unop` -/
@[to_additive (attr := simps) /-- Pull an additive subsemigroup back to an opposite subsemigroup
  along `AddOpposite.unop` -/]
/-
**Subsemigroup.op** 是 Mathlib 中的一个定义，位于命名空间 `Subsemigroup`。
形式化陈述：{M : Type u_2} → [inst : Mul M] → Subsemigroup M → Subsemigroup Mᵐᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def op (x : Subsemigroup M) : Subsemigroup Mᵐᵒᵖ where
  carrier := MulOpposite.unop ⁻¹' x
  mul_mem' ha hb := x.mul_mem hb ha

@[to_additive (attr := simp)]
/-
**Subsemigroup.mem_op** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：mem_op {x : Mᵐᵒᵖ} {S : Subsemigroup M} : x in S.op ↔ x.unop in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_op {x : Mᵐᵒᵖ} {S : Subsemigroup M} : x ∈ S.op ↔ x.unop ∈ S := Iff.rfl

/-- Pull an opposite subsemigroup back to a subsemigroup along `MulOpposite.op` -/
@[to_additive (attr := simps) /-- Pull an opposite additive subsemigroup back to a subsemigroup
  along `AddOpposite.op` -/]
/-
**Subsemigroup.unop** 是 Mathlib 中的一个定义，位于命名空间 `Subsemigroup`。
形式化陈述：{M : Type u_2} → [inst : Mul M] → Subsemigroup Mᵐᵒᵖ → Subsemigroup M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def unop (x : Subsemigroup Mᵐᵒᵖ) : Subsemigroup M where
  carrier := MulOpposite.op ⁻¹' x
  mul_mem' ha hb := x.mul_mem hb ha

@[to_additive (attr := simp)]
/-
**Subsemigroup.mem_unop** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：mem_unop {x : M} {S : Subsemigroup Mᵐᵒᵖ} : x in S.unop ↔ MulOpposite.op x 
in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_unop {x : M} {S : Subsemigroup Mᵐᵒᵖ} : x ∈ S.unop ↔ MulOpposite.op x ∈ S := Iff.rfl

@[to_additive (attr := simp)]
/-
**Subsemigroup.unop_op** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：unop_op (S : Subsemigroup M) : S.op.unop = S
参数：S : Subsemigroup M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_op (S : Subsemigroup M) : S.op.unop = S := rfl

@[to_additive (attr := simp)]
/-
**Subsemigroup.op_unop** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：op_unop (S : Subsemigroup Mᵐᵒᵖ) : S.unop.op = S
参数：S : Subsemigroup Mᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_unop (S : Subsemigroup Mᵐᵒᵖ) : S.unop.op = S := rfl

/-! ### Lattice results -/

@[to_additive]
/-
**Subsemigroup.op_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：op_le_iff {S₁ : Subsemigroup M} {S₂ : Subsemigroup Mᵐᵒᵖ} : S₁.op <= S₂ ↔ S
₁ <= S₂.unop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `MulOpposite.op_surjective`：op_surjective : Surjective (op : α -> αᵐᵒᵖ)

--- 原说明 ---
### Lattice results
-/
theorem op_le_iff {S₁ : Subsemigroup M} {S₂ : Subsemigroup Mᵐᵒᵖ} : S₁.op ≤ S₂ ↔ S₁ ≤ S₂.unop :=
  MulOpposite.op_surjective.forall

@[to_additive]
/-
**Subsemigroup.le_op_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：le_op_iff {S₁ : Subsemigroup Mᵐᵒᵖ} {S₂ : Subsemigroup M} : S₁ <= S₂.op ↔ S
₁.unop <= S₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `MulOpposite.op_surjective`：op_surjective : Surjective (op : α -> αᵐᵒᵖ)
-/
theorem le_op_iff {S₁ : Subsemigroup Mᵐᵒᵖ} {S₂ : Subsemigroup M} : S₁ ≤ S₂.op ↔ S₁.unop ≤ S₂ :=
  MulOpposite.op_surjective.forall

@[to_additive (attr := simp)]
/-
**Subsemigroup.op_le_op_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：op_le_op_iff {S₁ S₂ : Subsemigroup M} : S₁.op <= S₂.op ↔ S₁ <= S₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `MulOpposite.op_surjective`：op_surjective : Surjective (op : α -> αᵐᵒᵖ)
-/
theorem op_le_op_iff {S₁ S₂ : Subsemigroup M} : S₁.op ≤ S₂.op ↔ S₁ ≤ S₂ :=
  MulOpposite.op_surjective.forall

@[to_additive (attr := simp)]
/-
**Subsemigroup.unop_le_unop_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：unop_le_unop_iff {S₁ S₂ : Subsemigroup Mᵐᵒᵖ} : S₁.unop <= S₂.unop ↔ S₁ <= 
S₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `MulOpposite.unop_surjective`：unop_surjective : Surjective (unop : αᵐᵒᵖ -
> α)
-/
theorem unop_le_unop_iff {S₁ S₂ : Subsemigroup Mᵐᵒᵖ} : S₁.unop ≤ S₂.unop ↔ S₁ ≤ S₂ :=
  MulOpposite.unop_surjective.forall

/-- A subsemigroup `H` of `M` determines a subsemigroup `H.op` of the opposite semigroup `Mᵐᵒᵖ`. -/
@[to_additive (attr := simps) /-- An additive subsemigroup `H` of `M` determines an additive
  subsemigroup `H.op` of the opposite semigroup `Mᵐᵒᵖ`. -/]
/-
**Subsemigroup.opEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Subsemigroup`。
形式化陈述：opEquiv : Subsemigroup M ≃o Subsemigroup Mᵐᵒᵖ where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.unop_op`：unop_op (S : Subsemigroup M) : S.op.unop = S
· 使用定理 `Subsemigroup.op_unop`：op_unop (S : Subsemigroup Mᵐᵒᵖ) : S.unop.op = S
· 使用定理 `Subsemigroup.op_le_op_iff`：op_le_op_iff {S₁ S₂ : Subsemigroup M} : S₁.op
 <= S₂.op ↔ S₁ <= S₂
-/
def opEquiv : Subsemigroup M ≃o Subsemigroup Mᵐᵒᵖ where
  toFun := Subsemigroup.op
  invFun := Subsemigroup.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff

@[to_additive]
/-
**Subsemigroup.op_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：op_injective : (@Subsemigroup.op M _).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.injective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_
1 : LE β] (e : α ≃o β), Function.Injective ⇑e
-/
theorem op_injective : (@Subsemigroup.op M _).Injective := opEquiv.injective

@[to_additive]
/-
**Subsemigroup.unop_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：unop_injective : (@Subsemigroup.unop M _).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.injective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_
1 : LE β] (e : α ≃o β), Function.Injective ⇑e
-/
theorem unop_injective : (@Subsemigroup.unop M _).Injective := opEquiv.symm.injective

@[to_additive (attr := simp)]
/-
**Subsemigroup.op_inj** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：op_inj {S T : Subsemigroup M} : S.op = T.op ↔ S = T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.eq_iff_eq`：eq_iff_eq (f : r ≃r s) {a b} : f a = f b ↔ a = b
-/
theorem op_inj {S T : Subsemigroup M} : S.op = T.op ↔ S = T := opEquiv.eq_iff_eq

@[to_additive (attr := simp)]
/-
**Subsemigroup.unop_inj** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：unop_inj {S T : Subsemigroup Mᵐᵒᵖ} : S.unop = T.unop ↔ S = T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.eq_iff_eq`：eq_iff_eq (f : r ≃r s) {a b} : f a = f b ↔ a = b
-/
theorem unop_inj {S T : Subsemigroup Mᵐᵒᵖ} : S.unop = T.unop ↔ S = T := opEquiv.symm.eq_iff_eq

@[to_additive (attr := simp)]
/-
**Subsemigroup.op_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：op_bot : (⊥ : Subsemigroup M).op = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_bot`：OrderIso.map_bot [LE α] [PartialOrder β] [OrderBot α] 
[OrderBot β] (f : α ≃o β) : f ⊥ = ⊥
-/
theorem op_bot : (⊥ : Subsemigroup M).op = ⊥ := opEquiv.map_bot

@[to_additive (attr := simp)]
/-
**Subsemigroup.op_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：op_eq_bot {S : Subsemigroup M} : S.op = ⊥ ↔ S = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Subsemigroup.op_injective`：op_injective : (@Subsemigroup.op M _).Injecti
ve
· 使用定理 `Subsemigroup.op_bot`：op_bot : (⊥ : Subsemigroup M).op = ⊥
-/
theorem op_eq_bot {S : Subsemigroup M} : S.op = ⊥ ↔ S = ⊥ := op_injective.eq_iff' op_bot

@[to_additive (attr := simp)]
/-
**Subsemigroup.unop_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：unop_bot : (⊥ : Subsemigroup Mᵐᵒᵖ).unop = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_bot`：OrderIso.map_bot [LE α] [PartialOrder β] [OrderBot α] 
[OrderBot β] (f : α ≃o β) : f ⊥ = ⊥
-/
theorem unop_bot : (⊥ : Subsemigroup Mᵐᵒᵖ).unop = ⊥ := opEquiv.symm.map_bot

@[to_additive (attr := simp)]
/-
**Subsemigroup.unop_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：unop_eq_bot {S : Subsemigroup Mᵐᵒᵖ} : S.unop = ⊥ ↔ S = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Subsemigroup.unop_injective`：unop_injective : (@Subsemigroup.unop M _).I
njective
· 使用定理 `Subsemigroup.unop_bot`：unop_bot : (⊥ : Subsemigroup Mᵐᵒᵖ).unop = ⊥
-/
theorem unop_eq_bot {S : Subsemigroup Mᵐᵒᵖ} : S.unop = ⊥ ↔ S = ⊥ := unop_injective.eq_iff' unop_bot

@[to_additive (attr := simp)]
/-
**Subsemigroup.op_top** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：op_top : (⊤ : Subsemigroup M).op = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_top : (⊤ : Subsemigroup M).op = ⊤ := rfl

@[to_additive (attr := simp)]
/-
**Subsemigroup.op_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：op_eq_top {S : Subsemigroup M} : S.op = ⊤ ↔ S = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Subsemigroup.op_injective`：op_injective : (@Subsemigroup.op M _).Injecti
ve
· 使用定理 `Subsemigroup.op_top`：op_top : (⊤ : Subsemigroup M).op = ⊤
-/
theorem op_eq_top {S : Subsemigroup M} : S.op = ⊤ ↔ S = ⊤ := op_injective.eq_iff' op_top

@[to_additive (attr := simp)]
/-
**Subsemigroup.unop_top** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：unop_top : (⊤ : Subsemigroup Mᵐᵒᵖ).unop = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_top : (⊤ : Subsemigroup Mᵐᵒᵖ).unop = ⊤ := rfl

@[to_additive (attr := simp)]
/-
**Subsemigroup.unop_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：unop_eq_top {S : Subsemigroup Mᵐᵒᵖ} : S.unop = ⊤ ↔ S = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Subsemigroup.unop_injective`：unop_injective : (@Subsemigroup.unop M _).I
njective
· 使用定理 `Subsemigroup.unop_top`：unop_top : (⊤ : Subsemigroup Mᵐᵒᵖ).unop = ⊤
-/
theorem unop_eq_top {S : Subsemigroup Mᵐᵒᵖ} : S.unop = ⊤ ↔ S = ⊤ := unop_injective.eq_iff' unop_top

@[to_additive]
/-
**Subsemigroup.op_sup** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：op_sup (S₁ S₂ : Subsemigroup M) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op
参数：S₁ S₂ : Subsemigroup M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] [inst_1 : SemilatticeSup β] (f : α ≃o β) (x y : α),   f (x ⊔ y) = f x ⊔ f y
-/
theorem op_sup (S₁ S₂ : Subsemigroup M) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op :=
  opEquiv.map_sup _ _

@[to_additive]
/-
**Subsemigroup.unop_sup** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：unop_sup (S₁ S₂ : Subsemigroup Mᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop
参数：S₁ S₂ : Subsemigroup Mᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] [inst_1 : SemilatticeSup β] (f : α ≃o β) (x y : α),   f (x ⊔ y) = f x ⊔ f y
-/
theorem unop_sup (S₁ S₂ : Subsemigroup Mᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop :=
  opEquiv.symm.map_sup _ _

@[to_additive]
/-
**Subsemigroup.op_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：op_inf (S₁ S₂ : Subsemigroup M) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op
参数：S₁ S₂ : Subsemigroup M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_inf (S₁ S₂ : Subsemigroup M) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op := rfl

@[to_additive]
/-
**Subsemigroup.unop_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：unop_inf (S₁ S₂ : Subsemigroup Mᵐᵒᵖ) : (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop
参数：S₁ S₂ : Subsemigroup Mᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_inf (S₁ S₂ : Subsemigroup Mᵐᵒᵖ) : (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop := rfl

@[to_additive]
/-
**Subsemigroup.op_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：op_sSup (S : Set (Subsemigroup M)) : (sSup S).op = sSup (.unop ⁻¹' S)
参数：S : Set (Subsemigroup M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sSup_eq_sSup_symm_preimage`：OrderIso.map_sSup_eq_sSup_symm_
preimage [CompleteLattice β] (f : α ≃o β) (s : Set α) : f (sSup s) = sSup (f.sym
m ⁻¹' s)
-/
theorem op_sSup (S : Set (Subsemigroup M)) : (sSup S).op = sSup (.unop ⁻¹' S) :=
  opEquiv.map_sSup_eq_sSup_symm_preimage _

@[to_additive]
/-
**Subsemigroup.unop_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：unop_sSup (S : Set (Subsemigroup Mᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S)
参数：S : Set (Subsemigroup Mᵐᵒᵖ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sSup_eq_sSup_symm_preimage`：OrderIso.map_sSup_eq_sSup_symm_
preimage [CompleteLattice β] (f : α ≃o β) (s : Set α) : f (sSup s) = sSup (f.sym
m ⁻¹' s)
-/
theorem unop_sSup (S : Set (Subsemigroup Mᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) :=
  opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

@[to_additive]
/-
**Subsemigroup.op_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：op_sInf (S : Set (Subsemigroup M)) : (sInf S).op = sInf (.unop ⁻¹' S)
参数：S : Set (Subsemigroup M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sInf_eq_sInf_symm_preimage`：∀ {α : Type u_1} {β : Type u_2}
 [inst : CompleteLattice α] [inst_1 : CompleteLattice β] (f : α ≃o β) (s : Set α
),   f (sInf s) = sInf (⇑f.sy…
-/
theorem op_sInf (S : Set (Subsemigroup M)) : (sInf S).op = sInf (.unop ⁻¹' S) :=
  opEquiv.map_sInf_eq_sInf_symm_preimage _

@[to_additive]
/-
**Subsemigroup.unop_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：unop_sInf (S : Set (Subsemigroup Mᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S)
参数：S : Set (Subsemigroup Mᵐᵒᵖ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sInf_eq_sInf_symm_preimage`：∀ {α : Type u_1} {β : Type u_2}
 [inst : CompleteLattice α] [inst_1 : CompleteLattice β] (f : α ≃o β) (s : Set α
),   f (sInf s) = sInf (⇑f.sy…
-/
theorem unop_sInf (S : Set (Subsemigroup Mᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) :=
  opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

@[to_additive]
/-
**Subsemigroup.op_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：op_iSup (S : ι -> Subsemigroup M) : (iSup S).op = ⨆ i, (S i).op
参数：S : ι -> Subsemigroup M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_iSup`：OrderIso.map_iSup [CompleteLattice β] (f : α ≃o β) (x
 : ι -> α) : f (⨆ i, x i) = ⨆ i, f (x i)
-/
theorem op_iSup (S : ι → Subsemigroup M) : (iSup S).op = ⨆ i, (S i).op := opEquiv.map_iSup _

@[to_additive]
/-
**Subsemigroup.unop_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：unop_iSup (S : ι -> Subsemigroup Mᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop
参数：S : ι -> Subsemigroup Mᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_iSup`：OrderIso.map_iSup [CompleteLattice β] (f : α ≃o β) (x
 : ι -> α) : f (⨆ i, x i) = ⨆ i, f (x i)
-/
theorem unop_iSup (S : ι → Subsemigroup Mᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop :=
  opEquiv.symm.map_iSup _

@[to_additive]
/-
**Subsemigroup.op_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：op_iInf (S : ι -> Subsemigroup M) : (iInf S).op = ⨅ i, (S i).op
参数：S : ι -> Subsemigroup M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_iInf`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] (f : α ≃o β)   (x : ι → α), f 
(⨅ i, x…
-/
theorem op_iInf (S : ι → Subsemigroup M) : (iInf S).op = ⨅ i, (S i).op := opEquiv.map_iInf _

@[to_additive]
/-
**Subsemigroup.unop_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：unop_iInf (S : ι -> Subsemigroup Mᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop
参数：S : ι -> Subsemigroup Mᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_iInf`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] (f : α ≃o β)   (x : ι → α), f 
(⨅ i, x…
-/
theorem unop_iInf (S : ι → Subsemigroup Mᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop :=
  opEquiv.symm.map_iInf _

@[to_additive]
/-
**Subsemigroup.op_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：op_closure (s : Set M) : (closure s).op = closure (MulOpposite.unop ⁻¹' s)
参数：s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsemigroup.op_sInf`：op_sInf (S : Set (Subsemigroup M)) : (sInf S).op =
 sInf (.unop ⁻¹' S)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subsemigroup.coe_unop`：∀ {M : Type u_2} [inst : Mul M] (x : Subsemigroup
 Mᵐᵒᵖ), ↑x.unop = MulOpposite.op ⁻¹' ↑x
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `MulOpposite.unop_surjective`：unop_surjective : Surjective (unop : αᵐᵒᵖ -
> α)
-/
theorem op_closure (s : Set M) : (closure s).op = closure (MulOpposite.unop ⁻¹' s) := by
  simp_rw [closure, op_sInf, Set.preimage_ofPred_eq, Subsemigroup.coe_unop]
  congr with a
  exact MulOpposite.unop_surjective.forall

@[to_additive]
/-
**Subsemigroup.unop_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：unop_closure (s : Set Mᵐᵒᵖ) : (closure s).unop = closure (MulOpposite.op ⁻
¹' s)
参数：s : Set Mᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsemigroup.op_inj`：op_inj {S T : Subsemigroup M} : S.op = T.op ↔ S = T
· 使用定理 `Subsemigroup.op_unop`：op_unop (S : Subsemigroup Mᵐᵒᵖ) : S.unop.op = S
· 使用定理 `Subsemigroup.op_closure`：op_closure (s : Set M) : (closure s).op = closu
re (MulOpposite.unop ⁻¹' s)
· 使用定理 `Set.preimage_preimage`：preimage_preimage {g : β -> γ} {f : α -> β} {s : 
Set γ} : f ⁻¹' g ⁻¹' s = (fun x => g (f x)) ⁻¹' s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem unop_closure (s : Set Mᵐᵒᵖ) : (closure s).unop = closure (MulOpposite.op ⁻¹' s) := by
  rw [← op_inj, op_unop, op_closure]
  simp_rw [Set.preimage_preimage, MulOpposite.op_unop, Set.preimage_id']

/-- Bijection between a subsemigroup `H` and its opposite. -/
@[to_additive (attr := simps!) /-- Bijection between an additive subsemigroup `H` and its opposite.
  -/]
/-
**Subsemigroup.equivOp** 是 Mathlib 中的一个定义，位于命名空间 `Subsemigroup`。
形式化陈述：equivOp (H : Subsemigroup M) : H ≃ H.op
参数：H : Subsemigroup M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def equivOp (H : Subsemigroup M) : H ≃ H.op :=
  MulOpposite.opEquiv.subtypeEquiv fun _ => Iff.rfl

end Subsemigroup

