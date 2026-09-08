/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Algebra.Ring.Subsemiring.MulOpposite
public import Mathlib.Algebra.Ring.Subring.Basic

/-!

# Subring of opposite rings

For every ring `R`, we construct an equivalence between subrings of `R` and that of `Rᵐᵒᵖ`.

-/

@[expose] public section

namespace Subring

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

/-- Pull a subring back to an opposite subring along `MulOpposite.unop` -/
@[simps! coe toSubsemiring]
/-
**Subring.op** 是 Mathlib 中的一个定义，位于命名空间 `Subring`。
形式化陈述：{R : Type u_2} → [inst : NonAssocRing R] → Subring R → Subring Rᵐᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pull a subring back to an opposite subring along `MulOpposite.unop`
-/
protected def op (S : Subring R) : Subring Rᵐᵒᵖ where
  toSubsemiring := S.toSubsemiring.op
  neg_mem' := by simp

attribute [norm_cast] coe_op

@[simp]
/-
**Subring.mem_op** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mem_op {x : Rᵐᵒᵖ} {S : Subring R} : x in S.op ↔ x.unop in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_op {x : Rᵐᵒᵖ} {S : Subring R} : x ∈ S.op ↔ x.unop ∈ S := Iff.rfl

/-- Pull an opposite subring back to a subring along `MulOpposite.op` -/
@[simps! coe toSubsemiring]
/-
**Subring.unop** 是 Mathlib 中的一个定义，位于命名空间 `Subring`。
形式化陈述：{R : Type u_2} → [inst : NonAssocRing R] → Subring Rᵐᵒᵖ → Subring R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pull an opposite subring back to a subring along `MulOpposite.op`
-/
protected def unop (S : Subring Rᵐᵒᵖ) : Subring R where
  toSubsemiring := S.toSubsemiring.unop
  neg_mem' := by simp

attribute [norm_cast] coe_unop

@[simp]
/-
**Subring.mem_unop** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mem_unop {x : R} {S : Subring Rᵐᵒᵖ} : x in S.unop ↔ MulOpposite.op x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_unop {x : R} {S : Subring Rᵐᵒᵖ} : x ∈ S.unop ↔ MulOpposite.op x ∈ S := Iff.rfl

@[simp]
/-
**Subring.unop_op** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：unop_op (S : Subring R) : S.op.unop = S
参数：S : Subring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_op (S : Subring R) : S.op.unop = S := rfl

@[simp]
/-
**Subring.op_unop** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：op_unop (S : Subring Rᵐᵒᵖ) : S.unop.op = S
参数：S : Subring Rᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_unop (S : Subring Rᵐᵒᵖ) : S.unop.op = S := rfl

/-! ### Lattice results -/

/-
**Subring.op_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：op_le_iff {S₁ : Subring R} {S₂ : Subring Rᵐᵒᵖ} : S₁.op <= S₂ ↔ S₁ <= S₂.un
op
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `MulOpposite.op_surjective`：op_surjective : Surjective (op : α -> αᵐᵒᵖ)

--- 原说明 ---
### Lattice results
-/
theorem op_le_iff {S₁ : Subring R} {S₂ : Subring Rᵐᵒᵖ} : S₁.op ≤ S₂ ↔ S₁ ≤ S₂.unop :=
  MulOpposite.op_surjective.forall
/-
**Subring.le_op_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：le_op_iff {S₁ : Subring Rᵐᵒᵖ} {S₂ : Subring R} : S₁ <= S₂.op ↔ S₁.unop <= 
S₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `MulOpposite.op_surjective`：op_surjective : Surjective (op : α -> αᵐᵒᵖ)
-/
theorem le_op_iff {S₁ : Subring Rᵐᵒᵖ} {S₂ : Subring R} : S₁ ≤ S₂.op ↔ S₁.unop ≤ S₂ :=
  MulOpposite.op_surjective.forall

@[simp]
/-
**Subring.op_le_op_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：op_le_op_iff {S₁ S₂ : Subring R} : S₁.op <= S₂.op ↔ S₁ <= S₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `MulOpposite.op_surjective`：op_surjective : Surjective (op : α -> αᵐᵒᵖ)
-/
theorem op_le_op_iff {S₁ S₂ : Subring R} : S₁.op ≤ S₂.op ↔ S₁ ≤ S₂ :=
  MulOpposite.op_surjective.forall

@[simp]
/-
**Subring.unop_le_unop_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：unop_le_unop_iff {S₁ S₂ : Subring Rᵐᵒᵖ} : S₁.unop <= S₂.unop ↔ S₁ <= S₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `MulOpposite.unop_surjective`：unop_surjective : Surjective (unop : αᵐᵒᵖ -
> α)
-/
theorem unop_le_unop_iff {S₁ S₂ : Subring Rᵐᵒᵖ} : S₁.unop ≤ S₂.unop ↔ S₁ ≤ S₂ :=
  MulOpposite.unop_surjective.forall

/-- A subring `S` of `R` determines a subring `S.op` of the opposite ring `Rᵐᵒᵖ`. -/
@[simps]
/-
**Subring.opEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Subring`。
形式化陈述：opEquiv : Subring R ≃o Subring Rᵐᵒᵖ where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.unop_op`：unop_op (S : Subring R) : S.op.unop = S
· 使用定理 `Subring.op_unop`：op_unop (S : Subring Rᵐᵒᵖ) : S.unop.op = S
· 使用定理 `Subring.op_le_op_iff`：op_le_op_iff {S₁ S₂ : Subring R} : S₁.op <= S₂.op 
↔ S₁ <= S₂

--- 原说明 ---
A subring `S` of `R` determines a subring `S.op` of the opposite ring `Rᵐᵒᵖ`.
-/
def opEquiv : Subring R ≃o Subring Rᵐᵒᵖ where
  toFun := Subring.op
  invFun := Subring.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff
/-
**Subring.op_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：op_injective : (@Subring.op R _).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.injective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_
1 : LE β] (e : α ≃o β), Function.Injective ⇑e
-/
theorem op_injective : (@Subring.op R _).Injective := opEquiv.injective
/-
**Subring.unop_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：unop_injective : (@Subring.unop R _).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.injective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_
1 : LE β] (e : α ≃o β), Function.Injective ⇑e
-/
theorem unop_injective : (@Subring.unop R _).Injective := opEquiv.symm.injective
/-
**Subring.op_inj** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：∀ {R : Type u_2} [inst : NonAssocRing R] {S T : Subring R}, S.op = T.op ↔ 
S = T
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.eq_iff_eq`：eq_iff_eq (f : r ≃r s) {a b} : f a = f b ↔ a = b
-/
@[simp] theorem op_inj {S T : Subring R} : S.op = T.op ↔ S = T := opEquiv.eq_iff_eq
/-
**Subring.unop_inj** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：∀ {R : Type u_2} [inst : NonAssocRing R] {S T : Subring Rᵐᵒᵖ}, S.unop = T.
unop ↔ S = T
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.eq_iff_eq`：eq_iff_eq (f : r ≃r s) {a b} : f a = f b ↔ a = b
-/
@[simp] theorem unop_inj {S T : Subring Rᵐᵒᵖ} : S.unop = T.unop ↔ S = T := opEquiv.symm.eq_iff_eq

@[simp]
/-
**Subring.op_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：op_bot : (⊥ : Subring R).op = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_bot`：OrderIso.map_bot [LE α] [PartialOrder β] [OrderBot α] 
[OrderBot β] (f : α ≃o β) : f ⊥ = ⊥
-/
theorem op_bot : (⊥ : Subring R).op = ⊥ := opEquiv.map_bot

@[simp]
/-
**Subring.op_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：op_eq_bot {S : Subring R} : S.op = ⊥ ↔ S = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Subring.op_injective`：op_injective : (@Subring.op R _).Injective
· 使用定理 `Subring.op_bot`：op_bot : (⊥ : Subring R).op = ⊥
-/
theorem op_eq_bot {S : Subring R} : S.op = ⊥ ↔ S = ⊥ := op_injective.eq_iff' op_bot

@[simp]
/-
**Subring.unop_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：unop_bot : (⊥ : Subring Rᵐᵒᵖ).unop = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_bot`：OrderIso.map_bot [LE α] [PartialOrder β] [OrderBot α] 
[OrderBot β] (f : α ≃o β) : f ⊥ = ⊥
-/
theorem unop_bot : (⊥ : Subring Rᵐᵒᵖ).unop = ⊥ := opEquiv.symm.map_bot

@[simp]
/-
**Subring.unop_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：unop_eq_bot {S : Subring Rᵐᵒᵖ} : S.unop = ⊥ ↔ S = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Subring.unop_injective`：unop_injective : (@Subring.unop R _).Injective
· 使用定理 `Subring.unop_bot`：unop_bot : (⊥ : Subring Rᵐᵒᵖ).unop = ⊥
-/
theorem unop_eq_bot {S : Subring Rᵐᵒᵖ} : S.unop = ⊥ ↔ S = ⊥ := unop_injective.eq_iff' unop_bot

@[simp]
/-
**Subring.op_top** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：op_top : (⊤ : Subring R).op = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_top : (⊤ : Subring R).op = ⊤ := rfl

@[simp]
/-
**Subring.op_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：op_eq_top {S : Subring R} : S.op = ⊤ ↔ S = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Subring.op_injective`：op_injective : (@Subring.op R _).Injective
· 使用定理 `Subring.op_top`：op_top : (⊤ : Subring R).op = ⊤
-/
theorem op_eq_top {S : Subring R} : S.op = ⊤ ↔ S = ⊤ := op_injective.eq_iff' op_top

@[simp]
/-
**Subring.unop_top** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：unop_top : (⊤ : Subring Rᵐᵒᵖ).unop = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_top : (⊤ : Subring Rᵐᵒᵖ).unop = ⊤ := rfl

@[simp]
/-
**Subring.unop_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：unop_eq_top {S : Subring Rᵐᵒᵖ} : S.unop = ⊤ ↔ S = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Subring.unop_injective`：unop_injective : (@Subring.unop R _).Injective
· 使用定理 `Subring.unop_top`：unop_top : (⊤ : Subring Rᵐᵒᵖ).unop = ⊤
-/
theorem unop_eq_top {S : Subring Rᵐᵒᵖ} : S.unop = ⊤ ↔ S = ⊤ := unop_injective.eq_iff' unop_top
/-
**Subring.op_sup** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：op_sup (S₁ S₂ : Subring R) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op
参数：S₁ S₂ : Subring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] [inst_1 : SemilatticeSup β] (f : α ≃o β) (x y : α),   f (x ⊔ y) = f x ⊔ f y
-/
theorem op_sup (S₁ S₂ : Subring R) : (S₁ ⊔ S₂).op = S₁.op ⊔ S₂.op :=
  opEquiv.map_sup _ _
/-
**Subring.unop_sup** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：unop_sup (S₁ S₂ : Subring Rᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop
参数：S₁ S₂ : Subring Rᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] [inst_1 : SemilatticeSup β] (f : α ≃o β) (x y : α),   f (x ⊔ y) = f x ⊔ f y
-/
theorem unop_sup (S₁ S₂ : Subring Rᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop :=
  opEquiv.symm.map_sup _ _
/-
**Subring.op_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：op_inf (S₁ S₂ : Subring R) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op
参数：S₁ S₂ : Subring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_inf (S₁ S₂ : Subring R) : (S₁ ⊓ S₂).op = S₁.op ⊓ S₂.op := rfl
/-
**Subring.unop_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：unop_inf (S₁ S₂ : Subring Rᵐᵒᵖ) : (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop
参数：S₁ S₂ : Subring Rᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_inf (S₁ S₂ : Subring Rᵐᵒᵖ) : (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop := rfl
/-
**Subring.op_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：op_sSup (S : Set (Subring R)) : (sSup S).op = sSup (.unop ⁻¹' S)
参数：S : Set (Subring R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sSup_eq_sSup_symm_preimage`：OrderIso.map_sSup_eq_sSup_symm_
preimage [CompleteLattice β] (f : α ≃o β) (s : Set α) : f (sSup s) = sSup (f.sym
m ⁻¹' s)
-/
theorem op_sSup (S : Set (Subring R)) : (sSup S).op = sSup (.unop ⁻¹' S) :=
  opEquiv.map_sSup_eq_sSup_symm_preimage _
/-
**Subring.unop_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：unop_sSup (S : Set (Subring Rᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S)
参数：S : Set (Subring Rᵐᵒᵖ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sSup_eq_sSup_symm_preimage`：OrderIso.map_sSup_eq_sSup_symm_
preimage [CompleteLattice β] (f : α ≃o β) (s : Set α) : f (sSup s) = sSup (f.sym
m ⁻¹' s)
-/
theorem unop_sSup (S : Set (Subring Rᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) :=
  opEquiv.symm.map_sSup_eq_sSup_symm_preimage _
/-
**Subring.op_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：op_sInf (S : Set (Subring R)) : (sInf S).op = sInf (.unop ⁻¹' S)
参数：S : Set (Subring R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sInf_eq_sInf_symm_preimage`：∀ {α : Type u_1} {β : Type u_2}
 [inst : CompleteLattice α] [inst_1 : CompleteLattice β] (f : α ≃o β) (s : Set α
),   f (sInf s) = sInf (⇑f.sy…
-/
theorem op_sInf (S : Set (Subring R)) : (sInf S).op = sInf (.unop ⁻¹' S) :=
  opEquiv.map_sInf_eq_sInf_symm_preimage _
/-
**Subring.unop_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：unop_sInf (S : Set (Subring Rᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S)
参数：S : Set (Subring Rᵐᵒᵖ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sInf_eq_sInf_symm_preimage`：∀ {α : Type u_1} {β : Type u_2}
 [inst : CompleteLattice α] [inst_1 : CompleteLattice β] (f : α ≃o β) (s : Set α
),   f (sInf s) = sInf (⇑f.sy…
-/
theorem unop_sInf (S : Set (Subring Rᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) :=
  opEquiv.symm.map_sInf_eq_sInf_symm_preimage _
/-
**Subring.op_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：op_iSup (S : ι -> Subring R) : (iSup S).op = ⨆ i, (S i).op
参数：S : ι -> Subring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_iSup`：OrderIso.map_iSup [CompleteLattice β] (f : α ≃o β) (x
 : ι -> α) : f (⨆ i, x i) = ⨆ i, f (x i)
-/
theorem op_iSup (S : ι → Subring R) : (iSup S).op = ⨆ i, (S i).op := opEquiv.map_iSup _
/-
**Subring.unop_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：unop_iSup (S : ι -> Subring Rᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop
参数：S : ι -> Subring Rᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_iSup`：OrderIso.map_iSup [CompleteLattice β] (f : α ≃o β) (x
 : ι -> α) : f (⨆ i, x i) = ⨆ i, f (x i)
-/
theorem unop_iSup (S : ι → Subring Rᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop :=
  opEquiv.symm.map_iSup _
/-
**Subring.op_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：op_iInf (S : ι -> Subring R) : (iInf S).op = ⨅ i, (S i).op
参数：S : ι -> Subring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_iInf`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] (f : α ≃o β)   (x : ι → α), f 
(⨅ i, x…
-/
theorem op_iInf (S : ι → Subring R) : (iInf S).op = ⨅ i, (S i).op := opEquiv.map_iInf _
/-
**Subring.unop_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：unop_iInf (S : ι -> Subring Rᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop
参数：S : ι -> Subring Rᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_iInf`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] (f : α ≃o β)   (x : ι → α), f 
(⨅ i, x…
-/
theorem unop_iInf (S : ι → Subring Rᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop :=
  opEquiv.symm.map_iInf _
/-
**Subring.op_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：op_closure (s : Set R) : (closure s).op = closure (MulOpposite.unop ⁻¹' s)
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subring.op_sInf`：op_sInf (S : Set (Subring R)) : (sInf S).op = sInf (.un
op ⁻¹' S)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subring.coe_unop`：∀ {R : Type u_2} [inst : NonAssocRing R] (S : Subring 
Rᵐᵒᵖ), ↑S.unop = MulOpposite.op ⁻¹' ↑S
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
**Subring.unop_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：unop_closure (s : Set Rᵐᵒᵖ) : (closure s).unop = closure (MulOpposite.op ⁻
¹' s)
参数：s : Set Rᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subring.op_inj`：∀ {R : Type u_2} [inst : NonAssocRing R] {S T : Subring 
R}, S.op = T.op ↔ S = T
· 使用定理 `Subring.op_unop`：op_unop (S : Subring Rᵐᵒᵖ) : S.unop.op = S
· 使用定理 `Subring.op_closure`：op_closure (s : Set R) : (closure s).op = closure (M
ulOpposite.unop ⁻¹' s)
· 使用定理 `Set.preimage_preimage`：preimage_preimage {g : β -> γ} {f : α -> β} {s : 
Set γ} : f ⁻¹' g ⁻¹' s = (fun x => g (f x)) ⁻¹' s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem unop_closure (s : Set Rᵐᵒᵖ) : (closure s).unop = closure (MulOpposite.op ⁻¹' s) := by
  rw [← op_inj, op_unop, op_closure]
  simp_rw [Set.preimage_preimage, MulOpposite.op_unop, Set.preimage_id']

/-- Bijection between a subring `S` and its opposite. -/
@[simps!]
/-
**Subring.addEquivOp** 是 Mathlib 中的一个定义，位于命名空间 `Subring`。
形式化陈述：addEquivOp (S : Subring R) : S ≃+ S.op
参数：S : Subring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bijection between a subring `S` and its opposite.
-/
def addEquivOp (S : Subring R) : S ≃+ S.op := S.toSubsemiring.addEquivOp

/-- Bijection between a subring `S` and `MulOpposite` of its opposite. -/
@[simps!]
/-
**Subring.ringEquivOpMop** 是 Mathlib 中的一个定义，位于命名空间 `Subring`。
形式化陈述：ringEquivOpMop (S : Subring R) : S ≃+* (S.op)ᵐᵒᵖ
参数：S : Subring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bijection between a subring `S` and `MulOpposite` of its opposite.
-/
def ringEquivOpMop (S : Subring R) : S ≃+* (S.op)ᵐᵒᵖ := S.toSubsemiring.ringEquivOpMop

/-- Bijection between `MulOpposite` of a subring `S` and its opposite. -/
@[simps!]
/-
**Subring.mopRingEquivOp** 是 Mathlib 中的一个定义，位于命名空间 `Subring`。
形式化陈述：mopRingEquivOp (S : Subring R) : Sᵐᵒᵖ ≃+* S.op
参数：S : Subring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bijection between `MulOpposite` of a subring `S` and its opposite.
-/
def mopRingEquivOp (S : Subring R) : Sᵐᵒᵖ ≃+* S.op := S.toSubsemiring.mopRingEquivOp

end Subring

