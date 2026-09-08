/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Reid Barton, Simon Hudon, Kenny Lau
-/
module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Small.Defs

/-!
# Opposites

In this file we define a structure `Opposite α` containing a single field of type `α` and
two bijections `op : α → αᵒᵖ` and `unop : αᵒᵖ → α`. If `α` is a category, then `αᵒᵖ` is the
opposite category, with all arrows reversed.

-/

@[expose] public section


universe v u

-- morphism levels before object levels. See note [category theory universes].
variable (α : Sort u)

/-- The type of objects of the opposite of `α`; used to define the opposite category.

Now that Lean 4 supports definitional eta equality for records,
both `unop (op X) = X` and `op (unop X) = X` are definitional equalities.
-/
/-
**Opposite** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：Opposite where /-- The canonical map `α → αᵒᵖ`. -/ op :: /-- The canonical
 map `αᵒᵖ → α`. -/ unop : α  attribute [pp_nodot] Opposite.unop  /-- Make sure t
hat `Opposite.op a` is pretty-printed as `op a` instead of `{ unop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of objects of the opposite of `α`; used to define the opposite category
.

Now that Lean 4 supports definitional eta equality for records,
both `unop (op X) = X` and `op (unop X) = X` are definitional equalities. -/
-/
structure Opposite where
  /-- The canonical map `α → αᵒᵖ`. -/
  op ::
  /-- The canonical map `αᵒᵖ → α`. -/
  unop : α

attribute [pp_nodot] Opposite.unop

/-- Make sure that `Opposite.op a` is pretty-printed as `op a` instead of `{ unop := a }` or
`⟨a⟩`. -/
@[app_unexpander Opposite.op]
protected meta def Opposite.unexpander_op : Lean.PrettyPrinter.Unexpander
  | s => pure s

@[inherit_doc]
notation:max -- Use a high right binding power (like that of postfix ⁻¹) so that, for example,
-- `Presheaf Cᵒᵖ` parses as `Presheaf (Cᵒᵖ)` and not `(Presheaf C)ᵒᵖ`.
α "ᵒᵖ" => Opposite α

namespace Opposite

variable {α}

/-
**Opposite.op_injective** 是 Mathlib 中的一个定理，位于命名空间 `Opposite`。
形式化陈述：op_injective : Function.Injective (op : α -> αᵒᵖ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem op_injective : Function.Injective (op : α → αᵒᵖ) := fun _ _ => congr_arg Opposite.unop
/-
**Opposite.unop_injective** 是 Mathlib 中的一个定理，位于命名空间 `Opposite`。
形式化陈述：unop_injective : Function.Injective (unop : αᵒᵖ -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem unop_injective : Function.Injective (unop : αᵒᵖ → α) := fun _ _ h => congrArg op h

@[simp]
/-
**Opposite.op_unop** 是 Mathlib 中的一个定理，位于命名空间 `Opposite`。
形式化陈述：op_unop (x : αᵒᵖ) : op (unop x) = x
参数：x : αᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_unop (x : αᵒᵖ) : op (unop x) = x :=
  rfl
/-
**Opposite.unop_op** 是 Mathlib 中的一个定理，位于命名空间 `Opposite`。
形式化陈述：unop_op (x : α) : unop (op x) = x
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_op (x : α) : unop (op x) = x :=
  rfl

-- We could prove these by `Iff.rfl`, but that would make these eligible for `dsimp`. That would be
-- a bad idea because `Opposite` is irreducible.
/-
**Opposite.op_inj_iff** 是 Mathlib 中的一个定理，位于命名空间 `Opposite`。
形式化陈述：op_inj_iff (x y : α) : op x = op y ↔ x = y
参数：x y : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Opposite.op_injective`：op_injective : Function.Injective (op : α -> αᵒᵖ)
-/
theorem op_inj_iff (x y : α) : op x = op y ↔ x = y :=
  op_injective.eq_iff

@[simp]
/-
**Opposite.unop_inj_iff** 是 Mathlib 中的一个定理，位于命名空间 `Opposite`。
形式化陈述：unop_inj_iff (x y : αᵒᵖ) : unop x = unop y ↔ x = y
参数：x y : αᵒᵖ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Opposite.unop_injective`：unop_injective : Function.Injective (unop : αᵒᵖ
 -> α)
-/
theorem unop_inj_iff (x y : αᵒᵖ) : unop x = unop y ↔ x = y :=
  unop_injective.eq_iff

/-- The type-level equivalence between a type and its opposite. -/
/-
**Opposite.equivToOpposite** 是 Mathlib 中的一个定义，位于命名空间 `Opposite`。
形式化陈述：equivToOpposite : α ≃ αᵒᵖ where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Opposite.unop_op`：unop_op (x : α) : unop (op x) = x
· 使用定理 `Opposite.op_unop`：op_unop (x : αᵒᵖ) : op (unop x) = x

--- 原说明 ---
The type-level equivalence between a type and its opposite.
-/
def equivToOpposite : α ≃ αᵒᵖ where
  toFun := op
  invFun := unop
  left_inv := unop_op
  right_inv := op_unop
/-
**Opposite.op_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Opposite`。
形式化陈述：op_surjective : Function.Surjective (op : α -> αᵒᵖ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem op_surjective : Function.Surjective (op : α → αᵒᵖ) := equivToOpposite.surjective
/-
**Opposite.unop_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Opposite`。
形式化陈述：unop_surjective : Function.Surjective (unop : αᵒᵖ -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem unop_surjective : Function.Surjective (unop : αᵒᵖ → α) := equivToOpposite.symm.surjective

@[simp]
/-
**Opposite.equivToOpposite_coe** 是 Mathlib 中的一个定理，位于命名空间 `Opposite`。
形式化陈述：equivToOpposite_coe : (equivToOpposite : α -> αᵒᵖ) = op
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivToOpposite_coe : (equivToOpposite : α → αᵒᵖ) = op :=
  rfl

@[simp]
/-
**Opposite.equivToOpposite_symm_coe** 是 Mathlib 中的一个定理，位于命名空间 `Opposite`。
形式化陈述：equivToOpposite_symm_coe : (equivToOpposite.symm : αᵒᵖ -> α) = unop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem equivToOpposite_symm_coe : (equivToOpposite.symm : αᵒᵖ → α) = unop :=
  rfl
/-
**Opposite.op_eq_iff_eq_unop** 是 Mathlib 中的一个定理，位于命名空间 `Opposite`。
形式化陈述：op_eq_iff_eq_unop {x : α} {y} : op x = y ↔ x = unop y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem op_eq_iff_eq_unop {x : α} {y} : op x = y ↔ x = unop y :=
  equivToOpposite.eq_symm_apply.symm
/-
**Opposite.unop_eq_iff_eq_op** 是 Mathlib 中的一个定理，位于命名空间 `Opposite`。
形式化陈述：unop_eq_iff_eq_op {x} {y : α} : unop x = y ↔ x = op y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem unop_eq_iff_eq_op {x} {y : α} : unop x = y ↔ x = op y :=
  equivToOpposite.symm.eq_symm_apply.symm
/-
**Opposite.** 是 Mathlib 中的一个实例，位于命名空间 `Opposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : Inhabited αᵒᵖ :=
  ⟨op default⟩
/-
**Opposite.** 是 Mathlib 中的一个实例，位于命名空间 `Opposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] : Nonempty αᵒᵖ := Nonempty.map op ‹_›
/-
**Opposite.** 是 Mathlib 中的一个实例，位于命名空间 `Opposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton α] : Subsingleton αᵒᵖ := unop_injective.subsingleton

/-- If `X` is `u`-small, also `Xᵒᵖ` is `u`-small. -/
/-
**Opposite.small** 是 Mathlib 中的一个实例，位于命名空间 `Opposite`。
形式化陈述：small {X : Type v} [Small.{u} X] : Small.{u} Xᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Small.equiv_small`：∀ {α : Type v} [self : Small.{w, v} α], ∃ S, Nonempty
 (α ≃ S)
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `X` is `u`-small, also `Xᵒᵖ` is `u`-small.
-/
instance small {X : Type v} [Small.{u} X] : Small.{u} Xᵒᵖ := by
  obtain ⟨S, ⟨e⟩⟩ := Small.equiv_small (α := X)
  exact ⟨S, ⟨equivToOpposite.symm.trans e⟩⟩

end Opposite

