/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Logic.Equiv.Defs
public import Batteries.Tactic.Lint.Simp

/-!
# Multiplicative opposite and algebraic operations on it

In this file we define `MulOpposite α = αᵐᵒᵖ` to be the multiplicative opposite of `α`. It inherits
all additive algebraic structures on `α` (in other files), and reverses the order of multipliers in
multiplicative structures, i.e., `op (x * y) = op y * op x`, where `MulOpposite.op` is the
canonical map from `α` to `αᵐᵒᵖ`.

We also define `AddOpposite α = αᵃᵒᵖ` to be the additive opposite of `α`. It inherits all
multiplicative algebraic structures on `α` (in other files), and reverses the order of summands in
additive structures, i.e. `op (x + y) = op y + op x`, where `AddOpposite.op` is the canonical map
from `α` to `αᵃᵒᵖ`.

## Notation

* `αᵐᵒᵖ = MulOpposite α`
* `αᵃᵒᵖ = AddOpposite α`

## Implementation notes

In mathlib3 `αᵐᵒᵖ` was just a type synonym for `α`, marked irreducible after the API
was developed. In mathlib4 we use a structure with one field, because it is not possible
to change the reducibility of a declaration after its definition, and because Lean 4 has
definitional eta reduction for structures (Lean 3 does not).

## Tags

multiplicative opposite, additive opposite
-/

@[expose] public section

variable {α β : Type*}

open Function

/-- Auxiliary type to implement `MulOpposite` and `AddOpposite`.

It turns out to be convenient to have `MulOpposite α = AddOpposite α` true by definition, in the
same way that it is convenient to have `Additive α = α`; this means that we also get the defeq
`AddOpposite (Additive α) = MulOpposite α`, which is convenient when working with quotients.

This is a compromise between making `MulOpposite α = AddOpposite α = α` (what we had in Lean 3) and
having no defeqs within those three types (which we had as of https://github.com/leanprover-community/mathlib4/pull/1036). -/
/-
**PreOpposite** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_3 → Type u_3
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary type to implement `MulOpposite` and `AddOpposite`.

It turns out to be convenient to have `MulOpposite α = AddOpposite α` true by de
finition, in the
same way that it is convenient to have `Additive α = α`; this means that we also
 get the defeq
`AddOpposite (Additive α) = MulOpposite α`, which is convenient when working wit
h quotients.

This is a compromise between making `MulOpposite α = AddOpposite α = α` (what we
 had in Lean 3) and
having no defeqs within those three types (which we had as of https://github.com
/leanprover-community/mathlib4/pull/1036).
-/
structure PreOpposite (α : Type*) : Type _ where
  /-- The element of `PreOpposite α` that represents `x : α`. -/ op' ::
  /-- The element of `α` represented by `x : PreOpposite α`. -/ unop' : α

/-- Multiplicative opposite of a type. This type inherits all additive structures on `α` and
reverses left and right in multiplication. -/
@[to_additive
      /-- Additive opposite of a type. This type inherits all multiplicative structures on `α` and
      reverses left and right in addition. -/]
/-
**MulOpposite** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulOpposite (α : Type*) : Type _
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MulOpposite (α : Type*) : Type _ := PreOpposite α

/-- Multiplicative opposite of a type. -/
postfix:max "ᵐᵒᵖ" => MulOpposite

/-- Additive opposite of a type. -/
postfix:max "ᵃᵒᵖ" => AddOpposite

namespace MulOpposite

/-- The element of `MulOpposite α` that represents `x : α`. -/
-- implicit-reducible so that `op_star` can be `rfl`
@[to_additive /-- The element of `αᵃᵒᵖ` that represents `x : α`. -/, implicit_reducible]
/-
**MulOpposite.op** 是 Mathlib 中的一个定义，位于命名空间 `MulOpposite`。
形式化陈述：op : α -> αᵐᵒᵖ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def op : α → αᵐᵒᵖ :=
  PreOpposite.op'

/-- The element of `α` represented by `x : αᵐᵒᵖ`. -/
@[to_additive (attr := pp_nodot) /-- The element of `α` represented by `x : αᵃᵒᵖ`. -/,
  implicit_reducible] -- implicit-reducible so that `op_star` can be `rfl`
/-
**MulOpposite.unop** 是 Mathlib 中的一个定义，位于命名空间 `MulOpposite`。
形式化陈述：unop : αᵐᵒᵖ -> α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def unop : αᵐᵒᵖ → α :=
  PreOpposite.unop'

@[to_additive (attr := simp)]
/-
**MulOpposite.unop_op** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：unop_op (x : α) : unop (op x) = x
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_op (x : α) : unop (op x) = x := rfl

@[to_additive (attr := simp)]
/-
**MulOpposite.op_unop** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：op_unop (x : αᵐᵒᵖ) : op (unop x) = x
参数：x : αᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_unop (x : αᵐᵒᵖ) : op (unop x) = x :=
  rfl

@[to_additive (attr := simp)]
/-
**MulOpposite.op_comp_unop** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：op_comp_unop : (op : α -> αᵐᵒᵖ) ∘ unop = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_comp_unop : (op : α → αᵐᵒᵖ) ∘ unop = id :=
  rfl

@[to_additive (attr := simp)]
/-
**MulOpposite.unop_comp_op** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：unop_comp_op : (unop : αᵐᵒᵖ -> α) ∘ op = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_comp_op : (unop : αᵐᵒᵖ → α) ∘ op = id :=
  rfl

/-- A recursor for `MulOpposite`. Use as `induction x`. -/
@[to_additive (attr := simp, elab_as_elim, induction_eliminator, cases_eliminator)
  /-- A recursor for `AddOpposite`. Use as `induction x`. -/]
/-
**MulOpposite.rec'** 是 Mathlib 中的一个定义，位于命名空间 `MulOpposite`。
形式化陈述：{α : Type u_1} → {F : αᵐᵒᵖ → Sort u_3} → ((X : α) → F (MulOpposite.op X)) 
→ (X : αᵐᵒᵖ) → F X
参数：(X : α) → F (MulOpposite.op X)；X : αᵐᵒᵖ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def rec' {F : αᵐᵒᵖ → Sort*} (h : ∀ X, F (op X)) : ∀ X, F X := fun X ↦ h (unop X)

/-- The canonical bijection between `α` and `αᵐᵒᵖ`. -/
@[to_additive (attr := simps -fullyApplied apply symm_apply)
  /-- The canonical bijection between `α` and `αᵃᵒᵖ`. -/]
/-
**MulOpposite.opEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MulOpposite`。
形式化陈述：opEquiv : α ≃ αᵐᵒᵖ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.unop_op`：unop_op (x : α) : unop (op x) = x
· 使用定理 `MulOpposite.op_unop`：op_unop (x : αᵐᵒᵖ) : op (unop x) = x
-/
def opEquiv : α ≃ αᵐᵒᵖ :=
  ⟨op, unop, unop_op, op_unop⟩

@[to_additive]
/-
**MulOpposite.op_bijective** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：op_bijective : Bijective (op : α -> αᵐᵒᵖ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
theorem op_bijective : Bijective (op : α → αᵐᵒᵖ) :=
  opEquiv.bijective

@[to_additive]
/-
**MulOpposite.unop_bijective** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：unop_bijective : Bijective (unop : αᵐᵒᵖ -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem unop_bijective : Bijective (unop : αᵐᵒᵖ → α) :=
  opEquiv.symm.bijective

@[to_additive]
/-
**MulOpposite.op_injective** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：op_injective : Injective (op : α -> αᵐᵒᵖ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `MulOpposite.op_bijective`：op_bijective : Bijective (op : α -> αᵐᵒᵖ)
-/
theorem op_injective : Injective (op : α → αᵐᵒᵖ) :=
  op_bijective.injective

@[to_additive]
/-
**MulOpposite.op_surjective** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：op_surjective : Surjective (op : α -> αᵐᵒᵖ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `MulOpposite.op_bijective`：op_bijective : Bijective (op : α -> αᵐᵒᵖ)
-/
theorem op_surjective : Surjective (op : α → αᵐᵒᵖ) :=
  op_bijective.surjective

@[to_additive]
/-
**MulOpposite.unop_injective** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：unop_injective : Injective (unop : αᵐᵒᵖ -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `MulOpposite.unop_bijective`：unop_bijective : Bijective (unop : αᵐᵒᵖ -> α
)
-/
theorem unop_injective : Injective (unop : αᵐᵒᵖ → α) :=
  unop_bijective.injective

@[to_additive]
/-
**MulOpposite.unop_surjective** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：unop_surjective : Surjective (unop : αᵐᵒᵖ -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `MulOpposite.unop_bijective`：unop_bijective : Bijective (unop : αᵐᵒᵖ -> α
)
-/
theorem unop_surjective : Surjective (unop : αᵐᵒᵖ → α) :=
  unop_bijective.surjective

@[to_additive (attr := simp)]
/-
**MulOpposite.op_inj** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：op_inj {x y : α} : op x = op y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `PreOpposite.op'.injEq`：∀ {α : Type u_3} (unop' unop'_1 : α), ({ unop' :=
 unop' } = { unop' := unop'_1 }) = (unop' = unop'_1)
-/
theorem op_inj {x y : α} : op x = op y ↔ x = y := iff_of_eq <| PreOpposite.op'.injEq _ _

@[to_additive (attr := simp, nolint simpComm)]
/-
**MulOpposite.unop_inj** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：unop_inj {x y : αᵐᵒᵖ} : unop x = unop y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `MulOpposite.unop_injective`：unop_injective : Injective (unop : αᵐᵒᵖ -> α
)
-/
theorem unop_inj {x y : αᵐᵒᵖ} : unop x = unop y ↔ x = y :=
  unop_injective.eq_iff

attribute [nolint simpComm] AddOpposite.unop_inj
/-
**MulOpposite.** 是 Mathlib 中的一个引理，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma «forall» {p : αᵐᵒᵖ → Prop} : (∀ a, p a) ↔ ∀ a, p (op a) :=
  op_surjective.forall
/-
**MulOpposite.** 是 Mathlib 中的一个引理，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma «exists» {p : αᵐᵒᵖ → Prop} : (∃ a, p a) ↔ ∃ a, p (op a) :=
  op_surjective.exists
/-
**MulOpposite.instNontrivial** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [Nontrivial α], Nontrivial αᵐᵒᵖ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.nontrivial`：∀ {α : Type u_1} {β : Type u_2} [Nontrivi
al α] {f : α → β}, Function.Injective f → Nontrivial β
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
-/
@[to_additive] instance instNontrivial [Nontrivial α] : Nontrivial αᵐᵒᵖ := op_injective.nontrivial
/-
**MulOpposite.instInhabited** 是 Mathlib 中的一个定义，位于命名空间 `MulOpposite`。
形式化陈述：{α : Type u_1} → [Inhabited α] → Inhabited αᵐᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance instInhabited [Inhabited α] : Inhabited αᵐᵒᵖ := ⟨op default⟩

@[to_additive]
/-
**MulOpposite.instSubsingleton** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instSubsingleton [Subsingleton α] : Subsingleton αᵐᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β}, Function.Injective f → ∀ [Subsingleton β], Subsingleton α
· 使用定理 `MulOpposite.unop_injective`：unop_injective : Injective (unop : αᵐᵒᵖ -> α
)
-/
instance instSubsingleton [Subsingleton α] : Subsingleton αᵐᵒᵖ := unop_injective.subsingleton
/-
**MulOpposite.instUnique** 是 Mathlib 中的一个定义，位于命名空间 `MulOpposite`。
形式化陈述：{α : Type u_1} → [Unique α] → Unique αᵐᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance instUnique [Unique α] : Unique αᵐᵒᵖ := Unique.mk' _
/-
**MulOpposite.instIsEmpty** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [IsEmpty α], IsEmpty αᵐᵒᵖ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.isEmpty`：∀ {α : Sort u} {β : Sort v} [IsEmpty β] (f : α → β), I
sEmpty α
-/
@[to_additive] instance instIsEmpty [IsEmpty α] : IsEmpty αᵐᵒᵖ := Function.isEmpty unop

@[to_additive]
/-
**MulOpposite.instDecidableEq** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instDecidableEq [DecidableEq α] : DecidableEq αᵐᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.unop_injective`：unop_injective : Injective (unop : αᵐᵒᵖ -> α
)
-/
instance instDecidableEq [DecidableEq α] : DecidableEq αᵐᵒᵖ := unop_injective.decidableEq
/-
**MulOpposite.instZero** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instZero [Zero α] : Zero αᵐᵒᵖ where zero
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZero [Zero α] : Zero αᵐᵒᵖ where zero := op 0
/-
**MulOpposite.instOne** 是 Mathlib 中的一个定义，位于命名空间 `MulOpposite`。
形式化陈述：{α : Type u_1} → [One α] → One αᵐᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance instOne [One α] : One αᵐᵒᵖ where one := op 1
/-
**MulOpposite.instAdd** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instAdd [Add α] : Add αᵐᵒᵖ where add x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAdd [Add α] : Add αᵐᵒᵖ where add x y := op (unop x + unop y)
/-
**MulOpposite.instSub** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instSub [Sub α] : Sub αᵐᵒᵖ where sub x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSub [Sub α] : Sub αᵐᵒᵖ where sub x y := op (unop x - unop y)
/-
**MulOpposite.instNeg** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instNeg [Neg α] : Neg αᵐᵒᵖ where neg x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNeg [Neg α] : Neg αᵐᵒᵖ where neg x := op <| -unop x
/-
**MulOpposite.instInvolutiveNeg** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instInvolutiveNeg [InvolutiveNeg α] : InvolutiveNeg αᵐᵒᵖ where neg_neg _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInvolutiveNeg [InvolutiveNeg α] : InvolutiveNeg αᵐᵒᵖ where
  neg_neg _ := unop_injective <| neg_neg _
/-
**MulOpposite.instMul** 是 Mathlib 中的一个定义，位于命名空间 `MulOpposite`。
形式化陈述：{α : Type u_1} → [Mul α] → Mul αᵐᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance instMul [Mul α] : Mul αᵐᵒᵖ where mul x y := op (unop y * unop x)
/-
**MulOpposite.instInv** 是 Mathlib 中的一个定义，位于命名空间 `MulOpposite`。
形式化陈述：{α : Type u_1} → [Inv α] → Inv αᵐᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance instInv [Inv α] : Inv αᵐᵒᵖ where inv x := op <| (unop x)⁻¹

@[to_additive]
/-
**MulOpposite.instInvolutiveInv** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instInvolutiveInv [InvolutiveInv α] : InvolutiveInv αᵐᵒᵖ where inv_inv _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInvolutiveInv [InvolutiveInv α] : InvolutiveInv αᵐᵒᵖ where
  inv_inv _ := unop_injective <| inv_inv _
/-
**MulOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Add α] [IsLeftCancelAdd α] : IsLeftCancelAdd αᵐᵒᵖ where
  add_left_cancel _ _ _ eq := unop_injective <| add_left_cancel (congr_arg unop eq)
/-
**MulOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Add α] [IsRightCancelAdd α] : IsRightCancelAdd αᵐᵒᵖ where
  add_right_cancel _ _ _ eq := unop_injective <| add_right_cancel (congr_arg unop eq)
/-
**MulOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Add α] [IsCancelAdd α] : IsCancelAdd αᵐᵒᵖ where
/-
**MulOpposite.isLeftCancelAdd_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：isLeftCancelAdd_iff [Add α] : IsLeftCancelAdd αᵐᵒᵖ ↔ IsLeftCancelAdd α whe
re mp _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `add_left_cancel`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] {a 
b c : G}, a + b = a + c → b = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MulOpposite.instIsLeftCancelAdd`：∀ {α : Type u_1} [inst : Add α] [IsLeft
CancelAdd α], IsLeftCancelAdd αᵐᵒᵖ
-/
theorem isLeftCancelAdd_iff [Add α] : IsLeftCancelAdd αᵐᵒᵖ ↔ IsLeftCancelAdd α where
  mp _ := ⟨fun _ _ _ eq ↦ op_injective <| add_left_cancel (congr_arg op eq)⟩
  mpr _ := inferInstance
/-
**MulOpposite.isRightCancelAdd_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：isRightCancelAdd_iff [Add α] : IsRightCancelAdd αᵐᵒᵖ ↔ IsRightCancelAdd α 
where mp _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `add_right_cancel`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] {
a b c : G}, a + b = c + b → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MulOpposite.instIsRightCancelAdd`：∀ {α : Type u_1} [inst : Add α] [IsRig
htCancelAdd α], IsRightCancelAdd αᵐᵒᵖ
-/
theorem isRightCancelAdd_iff [Add α] : IsRightCancelAdd αᵐᵒᵖ ↔ IsRightCancelAdd α where
  mp _ := ⟨fun _ _ _ eq ↦ op_injective <| add_right_cancel (congr_arg op eq)⟩
  mpr _ := inferInstance
/-
**MulOpposite.isCancelAdd_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : Add α], IsCancelAdd αᵐᵒᵖ ↔ IsCancelAdd α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem isCancelAdd_iff [Add α] : IsCancelAdd αᵐᵒᵖ ↔ IsCancelAdd α := by
  simp_rw [isCancelAdd_iff, isLeftCancelAdd_iff, isRightCancelAdd_iff]
/-
**MulOpposite.instSMul** 是 Mathlib 中的一个定义，位于命名空间 `MulOpposite`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [SMul α β] → SMul α βᵐᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance instSMul [SMul α β] : SMul α βᵐᵒᵖ where smul c x := op (c • unop x)
/-
**MulOpposite.op_zero** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : Zero α], MulOpposite.op 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma op_zero [Zero α] : op (0 : α) = 0 := rfl
/-
**MulOpposite.unop_zero** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : Zero α], MulOpposite.unop 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unop_zero [Zero α] : unop (0 : αᵐᵒᵖ) = 0 := rfl
/-
**MulOpposite.op_one** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : One α], MulOpposite.op 1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma op_one [One α] : op (1 : α) = 1 := rfl
/-
**MulOpposite.unop_one** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : One α], MulOpposite.unop 1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma unop_one [One α] : unop (1 : αᵐᵒᵖ) = 1 := rfl
/-
**MulOpposite.op_add** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : Add α] (x y : α), MulOpposite.op (x + y) = MulOpp
osite.op x + MulOpposite.op y
参数：x y : α；x + y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma op_add [Add α] (x y : α) : op (x + y) = op x + op y := rfl
/-
**MulOpposite.unop_add** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : Add α] (x y : αᵐᵒᵖ), MulOpposite.unop (x + y) = M
ulOpposite.unop x + MulOpposite.unop y
参数：x y : αᵐᵒᵖ；x + y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unop_add [Add α] (x y : αᵐᵒᵖ) : unop (x + y) = unop x + unop y := rfl
/-
**MulOpposite.op_neg** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : Neg α] (x : α), MulOpposite.op (-x) = -MulOpposit
e.op x
参数：x : α；-x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma op_neg [Neg α] (x : α) : op (-x) = -op x := rfl
/-
**MulOpposite.unop_neg** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : Neg α] (x : αᵐᵒᵖ), MulOpposite.unop (-x) = -MulOp
posite.unop x
参数：x : αᵐᵒᵖ；-x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unop_neg [Neg α] (x : αᵐᵒᵖ) : unop (-x) = -unop x := rfl
/-
**MulOpposite.op_mul** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : Mul α] (x y : α), MulOpposite.op (x * y) = MulOpp
osite.op y * MulOpposite.op x
参数：x y : α；x * y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma op_mul [Mul α] (x y : α) : op (x * y) = op y * op x := rfl

@[to_additive (attr := simp)]
/-
**MulOpposite.unop_mul** 是 Mathlib 中的一个引理，位于命名空间 `MulOpposite`。
形式化陈述：unop_mul [Mul α] (x y : αᵐᵒᵖ) : unop (x * y) = unop y * unop x
参数：x y : αᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unop_mul [Mul α] (x y : αᵐᵒᵖ) : unop (x * y) = unop y * unop x := rfl
/-
**MulOpposite.op_inv** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : Inv α] (x : α), MulOpposite.op x⁻¹ = (MulOpposite
.op x)⁻¹
参数：x : α；MulOpposite.op x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma op_inv [Inv α] (x : α) : op x⁻¹ = (op x)⁻¹ := rfl
/-
**MulOpposite.unop_inv** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : Inv α] (x : αᵐᵒᵖ), MulOpposite.unop x⁻¹ = (MulOpp
osite.unop x)⁻¹
参数：x : αᵐᵒᵖ；MulOpposite.unop x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma unop_inv [Inv α] (x : αᵐᵒᵖ) : unop x⁻¹ = (unop x)⁻¹ := rfl
/-
**MulOpposite.op_sub** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : Sub α] (x y : α), MulOpposite.op (x - y) = MulOpp
osite.op x - MulOpposite.op y
参数：x y : α；x - y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma op_sub [Sub α] (x y : α) : op (x - y) = op x - op y := rfl
/-
**MulOpposite.unop_sub** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : Sub α] (x y : αᵐᵒᵖ), MulOpposite.unop (x - y) = M
ulOpposite.unop x - MulOpposite.unop y
参数：x y : αᵐᵒᵖ；x - y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unop_sub [Sub α] (x y : αᵐᵒᵖ) : unop (x - y) = unop x - unop y := rfl

@[to_additive (attr := simp)]
/-
**MulOpposite.op_smul** 是 Mathlib 中的一个引理，位于命名空间 `MulOpposite`。
形式化陈述：op_smul [SMul α β] (a : α) (b : β) : op (a • b) = a • op b
参数：a : α；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma op_smul [SMul α β] (a : α) (b : β) : op (a • b) = a • op b := rfl

@[to_additive (attr := simp)]
/-
**MulOpposite.unop_smul** 是 Mathlib 中的一个引理，位于命名空间 `MulOpposite`。
形式化陈述：unop_smul [SMul α β] (a : α) (b : βᵐᵒᵖ) : unop (a • b) = a • unop b
参数：a : α；b : βᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unop_smul [SMul α β] (a : α) (b : βᵐᵒᵖ) : unop (a • b) = a • unop b := rfl

@[simp, nolint simpComm]
/-
**MulOpposite.unop_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：unop_eq_zero_iff [Zero α] (a : αᵐᵒᵖ) : a.unop = (0 : α) ↔ a = (0 : αᵐᵒᵖ)
参数：a : αᵐᵒᵖ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `MulOpposite.unop_injective`：unop_injective : Injective (unop : αᵐᵒᵖ -> α
)
-/
theorem unop_eq_zero_iff [Zero α] (a : αᵐᵒᵖ) : a.unop = (0 : α) ↔ a = (0 : αᵐᵒᵖ) :=
  unop_injective.eq_iff' rfl

@[simp]
/-
**MulOpposite.op_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：op_eq_zero_iff [Zero α] (a : α) : op a = (0 : αᵐᵒᵖ) ↔ a = (0 : α)
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
-/
theorem op_eq_zero_iff [Zero α] (a : α) : op a = (0 : αᵐᵒᵖ) ↔ a = (0 : α) :=
  op_injective.eq_iff' rfl
/-
**MulOpposite.unop_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：unop_ne_zero_iff [Zero α] (a : αᵐᵒᵖ) : a.unop != (0 : α) ↔ a != (0 : αᵐᵒᵖ)
参数：a : αᵐᵒᵖ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `MulOpposite.unop_eq_zero_iff`：unop_eq_zero_iff [Zero α] (a : αᵐᵒᵖ) : a.u
nop = (0 : α) ↔ a = (0 : αᵐᵒᵖ)
-/
theorem unop_ne_zero_iff [Zero α] (a : αᵐᵒᵖ) : a.unop ≠ (0 : α) ↔ a ≠ (0 : αᵐᵒᵖ) :=
  not_congr <| unop_eq_zero_iff a
/-
**MulOpposite.op_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：op_ne_zero_iff [Zero α] (a : α) : op a != (0 : αᵐᵒᵖ) ↔ a != (0 : α)
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `MulOpposite.op_eq_zero_iff`：op_eq_zero_iff [Zero α] (a : α) : op a = (0 
: αᵐᵒᵖ) ↔ a = (0 : α)
-/
theorem op_ne_zero_iff [Zero α] (a : α) : op a ≠ (0 : αᵐᵒᵖ) ↔ a ≠ (0 : α) :=
  not_congr <| op_eq_zero_iff a

@[to_additive (attr := simp, nolint simpComm)]
/-
**MulOpposite.unop_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：unop_eq_one_iff [One α] (a : αᵐᵒᵖ) : a.unop = 1 ↔ a = 1
参数：a : αᵐᵒᵖ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `MulOpposite.unop_injective`：unop_injective : Injective (unop : αᵐᵒᵖ -> α
)
-/
theorem unop_eq_one_iff [One α] (a : αᵐᵒᵖ) : a.unop = 1 ↔ a = 1 :=
  unop_injective.eq_iff' rfl

attribute [nolint simpComm] AddOpposite.unop_eq_zero_iff

@[to_additive (attr := simp)]
/-
**MulOpposite.op_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `MulOpposite`。
形式化陈述：op_eq_one_iff [One α] (a : α) : op a = 1 ↔ a = 1
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
-/
lemma op_eq_one_iff [One α] (a : α) : op a = 1 ↔ a = 1 := op_injective.eq_iff

end MulOpposite

namespace AddOpposite

/-
**AddOpposite.instOne** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instOne [One α] : One αᵃᵒᵖ where one
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOne [One α] : One αᵃᵒᵖ where one := op 1
/-
**AddOpposite.op_one** 是 Mathlib 中的一个定理，位于命名空间 `AddOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : One α], AddOpposite.op 1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma op_one [One α] : op (1 : α) = 1 := rfl
/-
**AddOpposite.unop_one** 是 Mathlib 中的一个定理，位于命名空间 `AddOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : One α], AddOpposite.unop 1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unop_one [One α] : unop 1 = (1 : α) := rfl
/-
**AddOpposite.op_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `AddOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : One α] {a : α}, AddOpposite.op a = 1 ↔ a = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `AddOpposite.op_injective`：∀ {α : Type u_1}, Function.Injective AddOpposi
te.op
-/
@[simp] lemma op_eq_one_iff [One α] {a : α} : op a = 1 ↔ a = 1 := op_injective.eq_iff
/-
**AddOpposite.unop_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `AddOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : One α] {a : αᵃᵒᵖ}, AddOpposite.unop a = 1 ↔ a = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `AddOpposite.unop_injective`：∀ {α : Type u_1}, Function.Injective AddOppo
site.unop
-/
@[simp] lemma unop_eq_one_iff [One α] {a : αᵃᵒᵖ} : unop a = 1 ↔ a = 1 := unop_injective.eq_iff

attribute [nolint simpComm] unop_eq_one_iff
/-
**AddOpposite.instMul** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instMul [Mul α] : Mul αᵃᵒᵖ where mul a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMul [Mul α] : Mul αᵃᵒᵖ where mul a b := op (unop a * unop b)
/-
**AddOpposite.op_mul** 是 Mathlib 中的一个定理，位于命名空间 `AddOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : Mul α] (a b : α), AddOpposite.op (a * b) = AddOpp
osite.op a * AddOpposite.op b
参数：a b : α；a * b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma op_mul [Mul α] (a b : α) : op (a * b) = op a * op b := rfl
/-
**AddOpposite.unop_mul** 是 Mathlib 中的一个定理，位于命名空间 `AddOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : Mul α] (a b : αᵃᵒᵖ), AddOpposite.unop (a * b) = A
ddOpposite.unop a * AddOpposite.unop b
参数：a b : αᵃᵒᵖ；a * b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unop_mul [Mul α] (a b : αᵃᵒᵖ) : unop (a * b) = unop a * unop b := rfl
/-
**AddOpposite.instInv** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instInv [Inv α] : Inv αᵃᵒᵖ where inv a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInv [Inv α] : Inv αᵃᵒᵖ where inv a := op (unop a)⁻¹
/-
**AddOpposite.instInvolutiveInv** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instInvolutiveInv [InvolutiveInv α] : InvolutiveInv αᵃᵒᵖ where inv_inv _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInvolutiveInv [InvolutiveInv α] : InvolutiveInv αᵃᵒᵖ where
  inv_inv _ := unop_injective <| inv_inv _
/-
**AddOpposite.op_inv** 是 Mathlib 中的一个定理，位于命名空间 `AddOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : Inv α] (a : α), AddOpposite.op a⁻¹ = (AddOpposite
.op a)⁻¹
参数：a : α；AddOpposite.op a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma op_inv [Inv α] (a : α) : op a⁻¹ = (op a)⁻¹ := rfl
/-
**AddOpposite.unop_inv** 是 Mathlib 中的一个定理，位于命名空间 `AddOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : Inv α] (a : αᵃᵒᵖ), AddOpposite.unop a⁻¹ = (AddOpp
osite.unop a)⁻¹
参数：a : αᵃᵒᵖ；AddOpposite.unop a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unop_inv [Inv α] (a : αᵃᵒᵖ) : unop a⁻¹ = (unop a)⁻¹ := rfl
/-
**AddOpposite.instDiv** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instDiv [Div α] : Div αᵃᵒᵖ where div a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDiv [Div α] : Div αᵃᵒᵖ where div a b := op (unop a / unop b)
/-
**AddOpposite.op_div** 是 Mathlib 中的一个定理，位于命名空间 `AddOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : Div α] (a b : α), AddOpposite.op (a / b) = AddOpp
osite.op a / AddOpposite.op b
参数：a b : α；a / b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma op_div [Div α] (a b : α) : op (a / b) = op a / op b := rfl
/-
**AddOpposite.unop_div** 是 Mathlib 中的一个定理，位于命名空间 `AddOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : Div α] (a b : αᵃᵒᵖ), AddOpposite.unop (a / b) = A
ddOpposite.unop a / AddOpposite.unop b
参数：a b : αᵃᵒᵖ；a / b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unop_div [Div α] (a b : αᵃᵒᵖ) : unop (a / b) = unop a / unop b := rfl

end AddOpposite

