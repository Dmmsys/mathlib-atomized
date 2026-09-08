/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Algebra.Group.Submonoid.MulOpposite
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Opposite

/-!

# Subsemiring of opposite semirings

For every semiring `R`, we construct an equivalence between subsemirings of `R` and that of `Rᵐᵒᵖ`.

-/

@[expose] public section

namespace Subsemiring

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

/-- Pull a subsemiring back to an opposite subsemiring along `MulOpposite.unop` -/
@[simps! coe toSubmonoid]
/-
**Subsemiring.op** 是 Mathlib 中的一个定义，位于命名空间 `Subsemiring`。
形式化陈述：{R : Type u_2} → [inst : NonAssocSemiring R] → Subsemiring R → Subsemiring
 Rᵐᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pull a subsemiring back to an opposite subsemiring along `MulOpposite.unop`
-/
protected def op (S : Subsemiring R) : Subsemiring Rᵐᵒᵖ where
  toSubmonoid := S.toSubmonoid.op
  add_mem' hx hy := by simp_all [add_mem]
  zero_mem' := zero_mem S

attribute [norm_cast] coe_op

@[simp]
/-
**Subsemiring.mem_op** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：mem_op {x : Rᵐᵒᵖ} {S : Subsemiring R} : x in S.op ↔ x.unop in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_op {x : Rᵐᵒᵖ} {S : Subsemiring R} : x ∈ S.op ↔ x.unop ∈ S := Iff.rfl

/-- Pull an opposite subsemiring back to a subsemiring along `MulOpposite.op` -/
@[simps! coe toSubmonoid]
/-
**Subsemiring.unop** 是 Mathlib 中的一个定义，位于命名空间 `Subsemiring`。
形式化陈述：{R : Type u_2} → [inst : NonAssocSemiring R] → Subsemiring Rᵐᵒᵖ → Subsemir
ing R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pull an opposite subsemiring back to a subsemiring along `MulOpposite.op`
-/
protected def unop (S : Subsemiring Rᵐᵒᵖ) : Subsemiring R where
  toSubmonoid := S.toSubmonoid.unop
  add_mem' hx hy := by simp_all [add_mem]
  zero_mem' := zero_mem S

attribute [norm_cast] coe_unop

@[simp]
/-
**Subsemiring.mem_unop** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：mem_unop {x : R} {S : Subsemiring Rᵐᵒᵖ} : x in S.unop ↔ MulOpposite.op x i
n S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_unop {x : R} {S : Subsemiring Rᵐᵒᵖ} : x ∈ S.unop ↔ MulOpposite.op x ∈ S := Iff.rfl

@[simp]
/-
**Subsemiring.unop_op** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：unop_op (S : Subsemiring R) : S.op.unop = S
参数：S : Subsemiring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_op (S : Subsemiring R) : S.op.unop = S := rfl

@[simp]
/-
**Subsemiring.op_unop** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：op_unop (S : Subsemiring Rᵐᵒᵖ) : S.unop.op = S
参数：S : Subsemiring Rᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_unop (S : Subsemiring Rᵐᵒᵖ) : S.unop.op = S := rfl

/-! ### Lattice results -/

/-
**Subsemiring.op_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：op_le_iff {S₁ : Subsemiring R} {S₂ : Subsemiring Rᵐᵒᵖ} : S₁.op <= S₂ ↔ S₁ 
<= S₂.unop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `MulOpposite.op_surjective`：op_surjective : Surjective (op : α -> αᵐᵒᵖ)

--- 原说明 ---
### Lattice results
-/
theorem op_le_iff {S₁ : Subsemiring R} {S₂ : Subsemiring Rᵐᵒᵖ} : S₁.op ≤ S₂ ↔ S₁ ≤ S₂.unop :=
  MulOpposite.op_surjective.forall
/-
**Subsemiring.le_op_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：le_op_iff {S₁ : Subsemiring Rᵐᵒᵖ} {S₂ : Subsemiring R} : S₁ <= S₂.op ↔ S₁.
unop <= S₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `MulOpposite.op_surjective`：op_surjective : Surjective (op : α -> αᵐᵒᵖ)
-/
theorem le_op_iff {S₁ : Subsemiring Rᵐᵒᵖ} {S₂ : Subsemiring R} : S₁ ≤ S₂.op ↔ S₁.unop ≤ S₂ :=
  MulOpposite.op_surjective.forall

@[simp]
/-
**Subsemiring.op_le_op_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：op_le_op_iff {S₁ S₂ : Subsemiring R} : S₁.op <= S₂.op ↔ S₁ <= S₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `MulOpposite.op_surjective`：op_surjective : Surjective (op : α -> αᵐᵒᵖ)
-/
theorem op_le_op_iff {S₁ S₂ : Subsemiring R} : S₁.op ≤ S₂.op ↔ S₁ ≤ S₂ :=
  MulOpposite.op_surjective.forall

@[simp]
/-
**Subsemiring.unop_le_unop_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：unop_le_unop_iff {S₁ S₂ : Subsemiring Rᵐᵒᵖ} : S₁.unop <= S₂.unop ↔ S₁ <= S
₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `MulOpposite.unop_surjective`：unop_surjective : Surjective (unop : αᵐᵒᵖ -
> α)
-/
theorem unop_le_unop_iff {S₁ S₂ : Subsemiring Rᵐᵒᵖ} : S₁.unop ≤ S₂.unop ↔ S₁ ≤ S₂ :=
  MulOpposite.unop_surjective.forall

/-- A subsemiring `S` of `R` determines a subsemiring `S.op` of the opposite ring `Rᵐᵒᵖ`. -/
@[simps]
/-
**Subsemiring.opEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Subsemiring`。
形式化陈述：opEquiv : Subsemiring R ≃o Subsemiring Rᵐᵒᵖ where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.unop_op`：unop_op (S : Subsemiring R) : S.op.unop = S
· 使用定理 `Subsemiring.op_unop`：op_unop (S : Subsemiring Rᵐᵒᵖ) : S.unop.op = S
· 使用定理 `Subsemiring.op_le_op_iff`：op_le_op_iff {S₁ S₂ : Subsemiring R} : S₁.op <
= S₂.op ↔ S₁ <= S₂

--- 原说明 ---
A subsemiring `S` of `R` determines a subsemiring `S.op` of the opposite ring `R
ᵐᵒᵖ`.
-/
def opEquiv : Subsemiring R ≃o Subsemiring Rᵐᵒᵖ where
  toFun := Subsemiring.op
  invFun := Subsemiring.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff
/-
**Subsemiring.op_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：op_injective : (@Subsemiring.op R _).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.injective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_
1 : LE β] (e : α ≃o β), Function.Injective ⇑e
-/
theorem op_injective : (@Subsemiring.op R _).Injective := opEquiv.injective
/-
**Subsemiring.unop_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：unop_injective : (@Subsemiring.unop R _).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.injective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_
1 : LE β] (e : α ≃o β), Function.Injective ⇑e
-/
theorem unop_injective : (@Subsemiring.unop R _).Injective := opEquiv.symm.injective
/-
**Subsemiring.op_inj** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：∀ {R : Type u_2} [inst : NonAssocSemiring R] {S T : Subsemiring R}, S.op =
 T.op ↔ S = T
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.eq_iff_eq`：eq_iff_eq (f : r ≃r s) {a b} : f a = f b ↔ a = b
-/
@[simp] theorem op_inj {S T : Subsemiring R} : S.op = T.op ↔ S = T := opEquiv.eq_iff_eq

@[simp]
/-
**Subsemiring.unop_inj** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：unop_inj {S T : Subsemiring Rᵐᵒᵖ} : S.unop = T.unop ↔ S = T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.eq_iff_eq`：eq_iff_eq (f : r ≃r s) {a b} : f a = f b ↔ a = b
-/
theorem unop_inj {S T : Subsemiring Rᵐᵒᵖ} : S.unop = T.unop ↔ S = T := opEquiv.symm.eq_iff_eq

@[simp]
/-
**Subsemiring.op_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：op_bot : (⊥ : Subsemiring R).op = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_bot`：OrderIso.map_bot [LE α] [PartialOrder β] [OrderBot α] 
[OrderBot β] (f : α ≃o β) : f ⊥ = ⊥
-/
theorem op_bot : (⊥ : Subsemiring R).op = ⊥ := opEquiv.map_bot

@[simp]
/-
**Subsemiring.op_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：op_eq_bot {S : Subsemiring R} : S.op = ⊥ ↔ S = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Subsemiring.op_injective`：op_injective : (@Subsemiring.op R _).Injective
· 使用定理 `Subsemiring.op_bot`：op_bot : (⊥ : Subsemiring R).op = ⊥
-/
theorem op_eq_bot {S : Subsemiring R} : S.op = ⊥ ↔ S = ⊥ := op_injective.eq_iff' op_bot

@[simp]
/-
**Subsemiring.unop_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：unop_bot : (⊥ : Subsemiring Rᵐᵒᵖ).unop = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_bot`：OrderIso.map_bot [LE α] [PartialOrder β] [OrderBot α] 
[OrderBot β] (f : α ≃o β) : f ⊥ = ⊥
-/
theorem unop_bot : (⊥ : Subsemiring Rᵐᵒᵖ).unop = ⊥ := opEquiv.symm.map_bot

@[simp]
/-
**Subsemiring.unop_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：unop_eq_bot {S : Subsemiring Rᵐᵒᵖ} : S.unop = ⊥ ↔ S = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Subsemiring.unop_injective`：unop_injective : (@Subsemiring.unop R _).Inj
ective
· 使用定理 `Subsemiring.unop_bot`：unop_bot : (⊥ : Subsemiring Rᵐᵒᵖ).unop = ⊥
-/
theorem unop_eq_bot {S : Subsemiring Rᵐᵒᵖ} : S.unop = ⊥ ↔ S = ⊥ := unop_injective.eq_iff' unop_bot

@[simp]
/-
**Subsemiring.op_top** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：op_top : (⊤ : Subsemiring R).op = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_top : (⊤ : Subsemiring R).op = ⊤ := rfl

@[simp]
/-
**Subsemiring.op_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：op_eq_top {S : Subsemiring R} : S.op = ⊤ ↔ S = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Subsemiring.op_injective`：op_injective : (@Subsemiring.op R _).Injective
· 使用定理 `Subsemiring.op_top`：op_top : (⊤ : Subsemiring R).op = ⊤
-/
theorem op_eq_top {S : Subsemiring R} : S.op = ⊤ ↔ S = ⊤ := op_injective.eq_iff' op_top

@[simp]
/-
**Subsemiring.unop_top** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：unop_top : (⊤ : Subsemiring Rᵐᵒᵖ).unop = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_top : (⊤ : Subsemiring Rᵐᵒᵖ).unop = ⊤ := rfl

@[simp]
/-
**Subsemiring.unop_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：unop_eq_top {S : Subsemiring Rᵐᵒᵖ} : S.unop = ⊤ ↔ S = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Subsemiring.unop_injective`：unop_injective : (@Subsemiring.unop R _).Inj
ective
· 使用定理 `Subsemiring.unop_top`：unop_top : (⊤ : Subsemiring Rᵐᵒᵖ).unop = ⊤
-/
theorem unop_eq_top {S : Subsemiring Rᵐᵒᵖ} : S.unop = ⊤ ↔ S = ⊤ := unop_injective.eq_iff' unop_top
/-
**Subsemiring.op_sup** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：op_sup (S₁ S₂ : Subsemiring R) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op
参数：S₁ S₂ : Subsemiring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] [inst_1 : SemilatticeSup β] (f : α ≃o β) (x y : α),   f (x ⊔ y) = f x ⊔ f y
-/
theorem op_sup (S₁ S₂ : Subsemiring R) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op :=
  opEquiv.map_sup _ _
/-
**Subsemiring.unop_sup** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：unop_sup (S₁ S₂ : Subsemiring Rᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop
参数：S₁ S₂ : Subsemiring Rᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] [inst_1 : SemilatticeSup β] (f : α ≃o β) (x y : α),   f (x ⊔ y) = f x ⊔ f y
-/
theorem unop_sup (S₁ S₂ : Subsemiring Rᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop :=
  opEquiv.symm.map_sup _ _
/-
**Subsemiring.op_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：op_inf (S₁ S₂ : Subsemiring R) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op
参数：S₁ S₂ : Subsemiring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_inf (S₁ S₂ : Subsemiring R) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op := rfl
/-
**Subsemiring.unop_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：unop_inf (S₁ S₂ : Subsemiring Rᵐᵒᵖ) : (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop
参数：S₁ S₂ : Subsemiring Rᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_inf (S₁ S₂ : Subsemiring Rᵐᵒᵖ) : (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop := rfl
/-
**Subsemiring.op_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：op_sSup (S : Set (Subsemiring R)) : (sSup S).op = sSup (.unop ⁻¹' S)
参数：S : Set (Subsemiring R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sSup_eq_sSup_symm_preimage`：OrderIso.map_sSup_eq_sSup_symm_
preimage [CompleteLattice β] (f : α ≃o β) (s : Set α) : f (sSup s) = sSup (f.sym
m ⁻¹' s)
-/
theorem op_sSup (S : Set (Subsemiring R)) : (sSup S).op = sSup (.unop ⁻¹' S) :=
  opEquiv.map_sSup_eq_sSup_symm_preimage _
/-
**Subsemiring.unop_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：unop_sSup (S : Set (Subsemiring Rᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S)
参数：S : Set (Subsemiring Rᵐᵒᵖ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sSup_eq_sSup_symm_preimage`：OrderIso.map_sSup_eq_sSup_symm_
preimage [CompleteLattice β] (f : α ≃o β) (s : Set α) : f (sSup s) = sSup (f.sym
m ⁻¹' s)
-/
theorem unop_sSup (S : Set (Subsemiring Rᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) :=
  opEquiv.symm.map_sSup_eq_sSup_symm_preimage _
/-
**Subsemiring.op_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：op_sInf (S : Set (Subsemiring R)) : (sInf S).op = sInf (.unop ⁻¹' S)
参数：S : Set (Subsemiring R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sInf_eq_sInf_symm_preimage`：∀ {α : Type u_1} {β : Type u_2}
 [inst : CompleteLattice α] [inst_1 : CompleteLattice β] (f : α ≃o β) (s : Set α
),   f (sInf s) = sInf (⇑f.sy…
-/
theorem op_sInf (S : Set (Subsemiring R)) : (sInf S).op = sInf (.unop ⁻¹' S) :=
  opEquiv.map_sInf_eq_sInf_symm_preimage _
/-
**Subsemiring.unop_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：unop_sInf (S : Set (Subsemiring Rᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S)
参数：S : Set (Subsemiring Rᵐᵒᵖ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sInf_eq_sInf_symm_preimage`：∀ {α : Type u_1} {β : Type u_2}
 [inst : CompleteLattice α] [inst_1 : CompleteLattice β] (f : α ≃o β) (s : Set α
),   f (sInf s) = sInf (⇑f.sy…
-/
theorem unop_sInf (S : Set (Subsemiring Rᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) :=
  opEquiv.symm.map_sInf_eq_sInf_symm_preimage _
/-
**Subsemiring.op_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：op_iSup (S : ι -> Subsemiring R) : (iSup S).op = ⨆ i, (S i).op
参数：S : ι -> Subsemiring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_iSup`：OrderIso.map_iSup [CompleteLattice β] (f : α ≃o β) (x
 : ι -> α) : f (⨆ i, x i) = ⨆ i, f (x i)
-/
theorem op_iSup (S : ι → Subsemiring R) : (iSup S).op = ⨆ i, (S i).op := opEquiv.map_iSup _
/-
**Subsemiring.unop_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：unop_iSup (S : ι -> Subsemiring Rᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop
参数：S : ι -> Subsemiring Rᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_iSup`：OrderIso.map_iSup [CompleteLattice β] (f : α ≃o β) (x
 : ι -> α) : f (⨆ i, x i) = ⨆ i, f (x i)
-/
theorem unop_iSup (S : ι → Subsemiring Rᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop :=
  opEquiv.symm.map_iSup _
/-
**Subsemiring.op_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：op_iInf (S : ι -> Subsemiring R) : (iInf S).op = ⨅ i, (S i).op
参数：S : ι -> Subsemiring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_iInf`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] (f : α ≃o β)   (x : ι → α), f 
(⨅ i, x…
-/
theorem op_iInf (S : ι → Subsemiring R) : (iInf S).op = ⨅ i, (S i).op := opEquiv.map_iInf _
/-
**Subsemiring.unop_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：unop_iInf (S : ι -> Subsemiring Rᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop
参数：S : ι -> Subsemiring Rᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_iInf`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] (f : α ≃o β)   (x : ι → α), f 
(⨅ i, x…
-/
theorem unop_iInf (S : ι → Subsemiring Rᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop :=
  opEquiv.symm.map_iInf _
/-
**Subsemiring.op_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：op_closure (s : Set R) : (closure s).op = closure (MulOpposite.unop ⁻¹' s)
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsemiring.op_sInf`：op_sInf (S : Set (Subsemiring R)) : (sInf S).op = s
Inf (.unop ⁻¹' S)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subsemiring.coe_unop`：∀ {R : Type u_2} [inst : NonAssocSemiring R] (S : 
Subsemiring Rᵐᵒᵖ), ↑S.unop = MulOpposite.op ⁻¹' ↑S
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `MulOpposite.unop_surjective`：unop_surjective : Surjective (unop : αᵐᵒᵖ -
> α)
-/
theorem op_closure (s : Set R) : (closure s).op = closure (MulOpposite.unop ⁻¹' s) := by
  simp_rw [closure, op_sInf, Set.preimage_ofPred_eq, coe_unop]
  congr with a
  exact MulOpposite.unop_surjective.forall
/-
**Subsemiring.unop_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：unop_closure (s : Set Rᵐᵒᵖ) : (closure s).unop = closure (MulOpposite.op ⁻
¹' s)
参数：s : Set Rᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsemiring.op_inj`：∀ {R : Type u_2} [inst : NonAssocSemiring R] {S T : 
Subsemiring R}, S.op = T.op ↔ S = T
· 使用定理 `Subsemiring.op_unop`：op_unop (S : Subsemiring Rᵐᵒᵖ) : S.unop.op = S
· 使用定理 `Subsemiring.op_closure`：op_closure (s : Set R) : (closure s).op = closur
e (MulOpposite.unop ⁻¹' s)
· 使用定理 `Set.preimage_preimage`：preimage_preimage {g : β -> γ} {f : α -> β} {s : 
Set γ} : f ⁻¹' g ⁻¹' s = (fun x => g (f x)) ⁻¹' s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem unop_closure (s : Set Rᵐᵒᵖ) : (closure s).unop = closure (MulOpposite.op ⁻¹' s) := by
  rw [← op_inj, op_unop, op_closure]
  simp_rw [Set.preimage_preimage, MulOpposite.op_unop, Set.preimage_id']

/-- Bijection between a subsemiring `S` and its opposite. -/
@[simps!]
/-
**Subsemiring.addEquivOp** 是 Mathlib 中的一个定义，位于命名空间 `Subsemiring`。
形式化陈述：addEquivOp (S : Subsemiring R) : S ≃+ S.op where toEquiv
参数：S : Subsemiring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bijection between a subsemiring `S` and its opposite.
-/
def addEquivOp (S : Subsemiring R) : S ≃+ S.op where
  toEquiv := S.toSubmonoid.equivOp
  map_add' _ _ := rfl

-- TODO: Add this for `[Add]Submonoid` and `[Add]Subgroup`
/-- Bijection between a subsemiring `S` and `MulOpposite` of its opposite. -/
@[simps!]
/-
**Subsemiring.ringEquivOpMop** 是 Mathlib 中的一个定义，位于命名空间 `Subsemiring`。
形式化陈述：ringEquivOpMop (S : Subsemiring R) : S ≃+* (S.op)ᵐᵒᵖ where __
参数：S : Subsemiring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bijection between a subsemiring `S` and `MulOpposite` of its opposite.
-/
def ringEquivOpMop (S : Subsemiring R) : S ≃+* (S.op)ᵐᵒᵖ where
  __ := S.addEquivOp.trans MulOpposite.opAddEquiv
  map_mul' _ _ := rfl

-- TODO: Add this for `[Add]Submonoid` and `[Add]Subgroup`
/-- Bijection between `MulOpposite` of a subsemiring `S` and its opposite. -/
@[simps!]
/-
**Subsemiring.mopRingEquivOp** 是 Mathlib 中的一个定义，位于命名空间 `Subsemiring`。
形式化陈述：mopRingEquivOp (S : Subsemiring R) : Sᵐᵒᵖ ≃+* S.op where __
参数：S : Subsemiring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bijection between `MulOpposite` of a subsemiring `S` and its opposite.
-/
def mopRingEquivOp (S : Subsemiring R) : Sᵐᵒᵖ ≃+* S.op where
  __ := MulOpposite.opAddEquiv.symm.trans S.addEquivOp
  map_mul' _ _ := rfl

end Subsemiring

