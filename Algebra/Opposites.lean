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

/--
Definition of `PreOpposite` / `PreOpposite` 的定义

English:
structure PreOpposite
  parameters: (α : Type*)
  (no additional axioms)

中文:
结构 PreOpposite
  参数: (α : 类型)
  (无附加公理)
-/
structure PreOpposite (α : Type*) : Type _ where
  /-- The element of `PreOpposite α` that represents `x : α`. -/ op' ::
  /-- The element of `α` represented by `x : PreOpposite α`. -/ unop' : α

/-- Multiplicative opposite of a type. This type inherits all additive structures on `α` and
reverses left and right in multiplication. -/
@[to_additive
      /-- Additive opposite of a type. This type inherits all multiplicative structures on `α` and
      reverses left and right in addition. -/]
/--
Definition of `MulOpposite` / `MulOpposite` 的定义

English:
definition MulOpposite
  signature: (α : Type*)
  body: PreOpposite α

中文:
定义 MulOpposite
  签名: (α : 类型)
  定义体: PreOpposite α

Depends on / 依赖: PreOpposite
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
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: : α -> αᵐᵒᵖ
  body: PreOpposite.op'

中文:
定义 op
  签名: : α -> αᵐᵒᵖ
  定义体: PreOpposite.op'

Depends on / 依赖: PreOpposite, PreOpposite.op
-/
def op : α -> αᵐᵒᵖ :=
  PreOpposite.op'

/-- The element of `α` represented by `x : αᵐᵒᵖ`. -/
@[to_additive (attr := pp_nodot) /-- The element of `α` represented by `x : αᵃᵒᵖ`. -/,
  implicit_reducible] -- implicit-reducible so that `op_star` can be `rfl`
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: : αᵐᵒᵖ -> α
  body: PreOpposite.unop'

@[to_additive (attr := simp)]

中文:
定义 unop
  签名: : αᵐᵒᵖ -> α
  定义体: PreOpposite.unop'

@[to_additive (attr := simp)]

Depends on / 依赖: PreOpposite, PreOpposite.unop
-/
def unop : αᵐᵒᵖ -> α :=
  PreOpposite.unop'

@[to_additive (attr := simp)]
/--
theorem `unop_op` / 定理 `unop_op`

English:
theorem unop_op
  given: (x : α)
  statement: unop (op x) = x
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 unop_op
  条件: (x : α)
  结论: unop (op x) = x
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem unop_op (x : α) : unop (op x) = x := rfl

@[to_additive (attr := simp)]
/--
theorem `op_unop` / 定理 `op_unop`

English:
theorem op_unop
  given: (x : αᵐᵒᵖ)
  statement: op (unop x) = x
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 op_unop
  条件: (x : αᵐᵒᵖ)
  结论: op (unop x) = x
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem op_unop (x : αᵐᵒᵖ) : op (unop x) = x :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `op_comp_unop` / 定理 `op_comp_unop`

English:
theorem op_comp_unop
  statement: (op : α -> αᵐᵒᵖ) ∘ unop = id
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 op_comp_unop
  结论: (op : α -> αᵐᵒᵖ) ∘ unop = id
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem op_comp_unop : (op : α -> αᵐᵒᵖ) ∘ unop = id :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `unop_comp_op` / 定理 `unop_comp_op`

English:
theorem unop_comp_op
  statement: (unop : αᵐᵒᵖ -> α) ∘ op = id
  proof: rfl

中文:
定理 unop_comp_op
  结论: (unop : αᵐᵒᵖ -> α) ∘ op = id
  证明: rfl
-/
theorem unop_comp_op : (unop : αᵐᵒᵖ -> α) ∘ op = id :=
  rfl

/-- A recursor for `MulOpposite`. Use as `induction x`. -/
@[to_additive (attr := simp, elab_as_elim, induction_eliminator, cases_eliminator)
  /-- A recursor for `AddOpposite`. Use as `induction x`. -/]
/--
Definition of `rec'` / `rec'` 的定义

English:
definition rec'
  signature: {F : αᵐᵒᵖ -> Sort*} (h : forall X, F (op X))
  body: fun X => h (unop X)

中文:
定义 rec'
  签名: {F : αᵐᵒᵖ -> 类型层*} (h : 对任意 X, F (op X))
  定义体: fun X => h (unop X)
-/
protected def rec' {F : αᵐᵒᵖ -> Sort*} (h : forall X, F (op X)) : forall X, F X := fun X => h (unop X)

/-- The canonical bijection between `α` and `αᵐᵒᵖ`. -/
@[to_additive (attr := simps -fullyApplied apply symm_apply)
  /-- The canonical bijection between `α` and `αᵃᵒᵖ`. -/]
/--
Definition of `opEquiv` / `opEquiv` 的定义

English:
definition opEquiv
  signature: : α ≃ αᵐᵒᵖ
  body: ⟨op, unop, unop_op, op_unop⟩

@[to_additive]

中文:
定义 opEquiv
  签名: : α ≃ αᵐᵒᵖ
  定义体: ⟨op, unop, unop_op, op_unop⟩

@[to_additive]

Depends on / 依赖: op_unop, unop_op
-/
def opEquiv : α ≃ αᵐᵒᵖ :=
  ⟨op, unop, unop_op, op_unop⟩

@[to_additive]
/--
theorem `op_bijective` / 定理 `op_bijective`

English:
theorem op_bijective
  statement: Bijective (op : α -> αᵐᵒᵖ)
  proof: opEquiv.bijective

@[to_additive]

中文:
定理 op_bijective
  结论: 双射 (op : α -> αᵐᵒᵖ)
  证明: opEquiv.bijective

@[to_additive]

Depends on / 依赖: bijective, opEquiv, opEquiv.bijective
-/
theorem op_bijective : Bijective (op : α -> αᵐᵒᵖ) :=
  opEquiv.bijective

@[to_additive]
/--
theorem `unop_bijective` / 定理 `unop_bijective`

English:
theorem unop_bijective
  statement: Bijective (unop : αᵐᵒᵖ -> α)
  proof: opEquiv.symm.bijective

@[to_additive]

中文:
定理 unop_bijective
  结论: 双射 (unop : αᵐᵒᵖ -> α)
  证明: opEquiv.symm.bijective

@[to_additive]

Depends on / 依赖: bijective, opEquiv, opEquiv.symm.bijective
-/
theorem unop_bijective : Bijective (unop : αᵐᵒᵖ -> α) :=
  opEquiv.symm.bijective

@[to_additive]
/--
theorem `op_injective` / 定理 `op_injective`

English:
theorem op_injective
  statement: Injective (op : α -> αᵐᵒᵖ)
  proof: op_bijective.injective

@[to_additive]

中文:
定理 op_injective
  结论: 单射 (op : α -> αᵐᵒᵖ)
  证明: op_bijective.injective

@[to_additive]

Depends on / 依赖: injective, op_bijective, op_bijective.injective
-/
theorem op_injective : Injective (op : α -> αᵐᵒᵖ) :=
  op_bijective.injective

@[to_additive]
/--
theorem `op_surjective` / 定理 `op_surjective`

English:
theorem op_surjective
  statement: Surjective (op : α -> αᵐᵒᵖ)
  proof: op_bijective.surjective

@[to_additive]

中文:
定理 op_surjective
  结论: 满射 (op : α -> αᵐᵒᵖ)
  证明: op_bijective.surjective

@[to_additive]

Depends on / 依赖: op_bijective, op_bijective.surjective, surjective
-/
theorem op_surjective : Surjective (op : α -> αᵐᵒᵖ) :=
  op_bijective.surjective

@[to_additive]
/--
theorem `unop_injective` / 定理 `unop_injective`

English:
theorem unop_injective
  statement: Injective (unop : αᵐᵒᵖ -> α)
  proof: unop_bijective.injective

@[to_additive]

中文:
定理 unop_injective
  结论: 单射 (unop : αᵐᵒᵖ -> α)
  证明: unop_bijective.injective

@[to_additive]

Depends on / 依赖: injective, unop_bijective, unop_bijective.injective
-/
theorem unop_injective : Injective (unop : αᵐᵒᵖ -> α) :=
  unop_bijective.injective

@[to_additive]
/--
theorem `unop_surjective` / 定理 `unop_surjective`

English:
theorem unop_surjective
  statement: Surjective (unop : αᵐᵒᵖ -> α)
  proof: unop_bijective.surjective

@[to_additive (attr := simp)]

中文:
定理 unop_surjective
  结论: 满射 (unop : αᵐᵒᵖ -> α)
  证明: unop_bijective.surjective

@[to_additive (attr := simp)]

Depends on / 依赖: surjective, unop_bijective, unop_bijective.surjective
-/
theorem unop_surjective : Surjective (unop : αᵐᵒᵖ -> α) :=
  unop_bijective.surjective

@[to_additive (attr := simp)]
/--
theorem `op_inj` / 定理 `op_inj`

English:
theorem op_inj
  given: {x y : α}
  statement: op x = op y ↔ x = y
  proof: iff_of_eq PreOpposite.op'.injEq _ _

@[to_additive (attr := simp, nolint simpComm)]

中文:
定理 op_inj
  条件: {x y : α}
  结论: op x = op y ↔ x = y
  证明: iff_of_eq PreOpposite.op'.injEq _ _

@[to_additive (attr := simp, nolint simpComm)]

Depends on / 依赖: PreOpposite, PreOpposite.op, iff_of_eq
-/
theorem op_inj {x y : α} : op x = op y ↔ x = y := iff_of_eq PreOpposite.op'.injEq _ _

@[to_additive (attr := simp, nolint simpComm)]
/--
theorem `unop_inj` / 定理 `unop_inj`

English:
theorem unop_inj
  given: {x y : αᵐᵒᵖ}
  statement: unop x = unop y ↔ x = y
  proof: unop_injective.eq_iff

中文:
定理 unop_inj
  条件: {x y : αᵐᵒᵖ}
  结论: unop x = unop y ↔ x = y
  证明: unop_injective.eq_iff

Depends on / 依赖: eq_iff, unop_injective, unop_injective.eq_iff
-/
theorem unop_inj {x y : αᵐᵒᵖ} : unop x = unop y ↔ x = y :=
  unop_injective.eq_iff

attribute [nolint simpComm] AddOpposite.unop_inj

/--
lemma `«forall»` / 引理 `«forall»`

English:
lemma «forall»
  given: {p : αᵐᵒᵖ -> Prop}
  statement: (forall a, p a) ↔ forall a, p (op a)
  proof: op_surjective.forall

中文:
引理 «对任意»
  条件: {p : αᵐᵒᵖ -> 命题}
  结论: (对任意 a, p a) ↔ 对任意 a, p (op a)
  证明: op_surjective.forall
-/
@[to_additive (attr := simp)] lemma «forall» {p : αᵐᵒᵖ -> Prop} : (forall a, p a) ↔ forall a, p (op a) :=
  op_surjective.forall

/--
lemma `«exists»` / 引理 `«exists»`

English:
lemma «exists»
  given: {p : αᵐᵒᵖ -> Prop}
  statement: (exists a, p a) ↔ exists a, p (op a)
  proof: op_surjective.exists

中文:
引理 «存在»
  条件: {p : αᵐᵒᵖ -> 命题}
  结论: (存在 a, p a) ↔ 存在 a, p (op a)
  证明: op_surjective.exists
-/
@[to_additive (attr := simp)] lemma «exists» {p : αᵐᵒᵖ -> Prop} : (exists a, p a) ↔ exists a, p (op a) :=
  op_surjective.exists

/--
Instance `instNontrivial` / 实例 `instNontrivial`

English:
instance instNontrivial
  signature: [Nontrivial α]
  body: op_injective.nontrivial

中文:
实例 instNontrivial
  签名: [非平凡 α]
  定义体: op_injective.nontrivial
-/
@[to_additive] instance instNontrivial [Nontrivial α] : Nontrivial αᵐᵒᵖ := op_injective.nontrivial

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: [Inhabited α]
  body: ⟨op default⟩

@[to_additive]

中文:
实例 instInhabited
  签名: [可居 α]
  定义体: ⟨op default⟩

@[to_additive]
-/
@[to_additive] instance instInhabited [Inhabited α] : Inhabited αᵐᵒᵖ := ⟨op default⟩

@[to_additive]
/--
Instance `instSubsingleton` / 实例 `instSubsingleton`

English:
instance instSubsingleton
  signature: [Subsingleton α]
  body: unop_injective.subsingleton

中文:
实例 instSubsingleton
  签名: [子单例 α]
  定义体: unop_injective.subsingleton

Depends on / 依赖: subsingleton, unop_injective, unop_injective.subsingleton
-/
instance instSubsingleton [Subsingleton α] : Subsingleton αᵐᵒᵖ := unop_injective.subsingleton

/--
Instance `instUnique` / 实例 `instUnique`

English:
instance instUnique
  signature: [Unique α]
  body: Unique.mk' _

中文:
实例 instUnique
  签名: [唯一 α]
  定义体: Unique.mk' _
-/
@[to_additive] instance instUnique [Unique α] : Unique αᵐᵒᵖ := Unique.mk' _

/--
Instance `instIsEmpty` / 实例 `instIsEmpty`

English:
instance instIsEmpty
  signature: [IsEmpty α]
  body: Function.isEmpty unop

@[to_additive]

中文:
实例 instIsEmpty
  签名: [是空 α]
  定义体: Function.isEmpty unop

@[to_additive]
-/
@[to_additive] instance instIsEmpty [IsEmpty α] : IsEmpty αᵐᵒᵖ := Function.isEmpty unop

@[to_additive]
/--
Instance `instDecidableEq` / 实例 `instDecidableEq`

English:
instance instDecidableEq
  signature: [DecidableEq α]
  body: unop_injective.decidableEq

中文:
实例 instDecidableEq
  签名: [DecidableEq α]
  定义体: unop_injective.decidableEq

Depends on / 依赖: decidableEq, unop_injective, unop_injective.decidableEq
-/
instance instDecidableEq [DecidableEq α] : DecidableEq αᵐᵒᵖ := unop_injective.decidableEq

/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: [Zero α]
  body: op 0

中文:
实例 instZero
  签名: [零 α]
  定义体: op 0
-/
instance instZero [Zero α] : Zero αᵐᵒᵖ where zero := op 0

/--
Instance `instOne` / 实例 `instOne`

English:
instance instOne
  signature: [One α]
  body: op 1

中文:
实例 instOne
  签名: [幺 α]
  定义体: op 1
-/
@[to_additive] instance instOne [One α] : One αᵐᵒᵖ where one := op 1

/--
Instance `instAdd` / 实例 `instAdd`

English:
instance instAdd
  signature: [Add α]
  body: op (unop x + unop y)

中文:
实例 instAdd
  签名: [加法 α]
  定义体: op (unop x + unop y)
-/
instance instAdd [Add α] : Add αᵐᵒᵖ where add x y := op (unop x + unop y)
/--
Instance `instSub` / 实例 `instSub`

English:
instance instSub
  signature: [Sub α]
  body: op (unop x - unop y)

中文:
实例 instSub
  签名: [减法 α]
  定义体: op (unop x - unop y)
-/
instance instSub [Sub α] : Sub αᵐᵒᵖ where sub x y := op (unop x - unop y)
/--
Instance `instNeg` / 实例 `instNeg`

English:
instance instNeg
  signature: [Neg α]
  body: op -unop x

中文:
实例 instNeg
  签名: [取负 α]
  定义体: op -unop x
-/
instance instNeg [Neg α] : Neg αᵐᵒᵖ where neg x := op -unop x

/--
Instance `instInvolutiveNeg` / 实例 `instInvolutiveNeg`

English:
instance instInvolutiveNeg
  signature: [InvolutiveNeg α]
  body: unop_injective neg_neg _

中文:
实例 instInvolutiveNeg
  签名: [InvolutiveNeg α]
  定义体: unop_injective neg_neg _

Depends on / 依赖: neg_neg, unop_injective
-/
instance instInvolutiveNeg [InvolutiveNeg α] : InvolutiveNeg αᵐᵒᵖ where
neg_neg _ := unop_injective neg_neg _

/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: [Mul α]
  body: op (unop y * unop x)

中文:
实例 instMul
  签名: [乘法 α]
  定义体: op (unop y * unop x)
-/
@[to_additive] instance instMul [Mul α] : Mul αᵐᵒᵖ where mul x y := op (unop y * unop x)
/--
Instance `instInv` / 实例 `instInv`

English:
instance instInv
  signature: [Inv α]
  body: op (unop x)⁻¹

@[to_additive]

中文:
实例 instInv
  签名: [取逆 α]
  定义体: op (unop x)⁻¹

@[to_additive]
-/
@[to_additive] instance instInv [Inv α] : Inv αᵐᵒᵖ where inv x := op (unop x)⁻¹

@[to_additive]
/--
Instance `instInvolutiveInv` / 实例 `instInvolutiveInv`

English:
instance instInvolutiveInv
  signature: [InvolutiveInv α]
  body: unop_injective inv_inv _

中文:
实例 instInvolutiveInv
  签名: [InvolutiveInv α]
  定义体: unop_injective inv_inv _

Depends on / 依赖: inv_inv, unop_injective
-/
instance instInvolutiveInv [InvolutiveInv α] : InvolutiveInv αᵐᵒᵖ where
inv_inv _ := unop_injective inv_inv _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Add
  signature: α] [IsLeftCancelAdd α] : IsLeftCancelAdd αᵐᵒᵖ where
  body: unop_injective add_left_cancel (congr_arg unop eq)

中文:
实例 [加法
  签名: α] [是左消去加法 α] : 是左消去加法 αᵐᵒᵖ where
  定义体: unop_injective add_left_cancel (congr_arg unop eq)

Depends on / 依赖: add_left_cancel, congr_arg, unop_injective
-/
instance [Add α] [IsLeftCancelAdd α] : IsLeftCancelAdd αᵐᵒᵖ where
add_left_cancel _ _ _ eq := unop_injective add_left_cancel (congr_arg unop eq)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Add
  signature: α] [IsRightCancelAdd α] : IsRightCancelAdd αᵐᵒᵖ where
  body: unop_injective add_right_cancel (congr_arg unop eq)

中文:
实例 [加法
  签名: α] [是右消去加法 α] : 是右消去加法 αᵐᵒᵖ where
  定义体: unop_injective add_right_cancel (congr_arg unop eq)

Depends on / 依赖: add_right_cancel, congr_arg, unop_injective
-/
instance [Add α] [IsRightCancelAdd α] : IsRightCancelAdd αᵐᵒᵖ where
add_right_cancel _ _ _ eq := unop_injective add_right_cancel (congr_arg unop eq)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Add
  signature: α] [IsCancelAdd α] : IsCancelAdd αᵐᵒᵖ where

中文:
实例 [加法
  签名: α] [是消去加法 α] : 是消去加法 αᵐᵒᵖ where
-/
instance [Add α] [IsCancelAdd α] : IsCancelAdd αᵐᵒᵖ where

/--
theorem `isLeftCancelAdd_iff` / 定理 `isLeftCancelAdd_iff`

English:
theorem isLeftCancelAdd_iff
  given: [Add α]
  statement: IsLeftCancelAdd αᵐᵒᵖ ↔ IsLeftCancelAdd α where
  proof: ⟨fun _ _ _ eq => op_injective add_left_cancel (congr_arg op eq)⟩
  mpr _ := inferInstance

中文:
定理 isLeftCancelAdd_iff
  条件: [加法 α]
  结论: 是左消去加法 αᵐᵒᵖ ↔ 是左消去加法 α where
  证明: ⟨fun _ _ _ eq => op_injective add_left_cancel (congr_arg op eq)⟩
  mpr _ := inferInstance

Depends on / 依赖: add_left_cancel, congr_arg, op_injective
-/
theorem isLeftCancelAdd_iff [Add α] : IsLeftCancelAdd αᵐᵒᵖ ↔ IsLeftCancelAdd α where
mp _ := ⟨fun _ _ _ eq => op_injective add_left_cancel (congr_arg op eq)⟩
  mpr _ := inferInstance

/--
theorem `isRightCancelAdd_iff` / 定理 `isRightCancelAdd_iff`

English:
theorem isRightCancelAdd_iff
  given: [Add α]
  statement: IsRightCancelAdd αᵐᵒᵖ ↔ IsRightCancelAdd α where
  proof: ⟨fun _ _ _ eq => op_injective add_right_cancel (congr_arg op eq)⟩
  mpr _ := inferInstance

中文:
定理 isRightCancelAdd_iff
  条件: [加法 α]
  结论: 是右消去加法 αᵐᵒᵖ ↔ 是右消去加法 α where
  证明: ⟨fun _ _ _ eq => op_injective add_right_cancel (congr_arg op eq)⟩
  mpr _ := inferInstance

Depends on / 依赖: add_right_cancel, congr_arg, op_injective
-/
theorem isRightCancelAdd_iff [Add α] : IsRightCancelAdd αᵐᵒᵖ ↔ IsRightCancelAdd α where
mp _ := ⟨fun _ _ _ eq => op_injective add_right_cancel (congr_arg op eq)⟩
  mpr _ := inferInstance

/--
theorem `isCancelAdd_iff` / 定理 `isCancelAdd_iff`

English:
theorem isCancelAdd_iff
  given: [Add α]
  statement: IsCancelAdd αᵐᵒᵖ ↔ IsCancelAdd α
  proof: by
  simp_rw [isCancelAdd_iff, isLeftCancelAdd_iff, isRightCancelAdd_iff]

中文:
定理 isCancelAdd_iff
  条件: [加法 α]
  结论: 是消去加法 αᵐᵒᵖ ↔ 是消去加法 α
  证明: by
  simp_rw [isCancelAdd_iff, isLeftCancelAdd_iff, isRightCancelAdd_iff]
-/
protected theorem isCancelAdd_iff [Add α] : IsCancelAdd αᵐᵒᵖ ↔ IsCancelAdd α := by
  simp_rw [isCancelAdd_iff, isLeftCancelAdd_iff, isRightCancelAdd_iff]

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: [SMul α β]
  body: op (c • unop x)

中文:
实例 instSMul
  签名: [标量乘法 α β]
  定义体: op (c • unop x)
-/
@[to_additive] instance instSMul [SMul α β] : SMul α βᵐᵒᵖ where smul c x := op (c • unop x)

/--
lemma `op_zero` / 引理 `op_zero`

English:
lemma op_zero
  given: [Zero α]
  statement: op (0 : α) = 0
  proof: rfl

中文:
引理 op_zero
  条件: [零 α]
  结论: op (0 : α) = 0
  证明: rfl
-/
@[simp] lemma op_zero [Zero α] : op (0 : α) = 0 := rfl

/--
lemma `unop_zero` / 引理 `unop_zero`

English:
lemma unop_zero
  given: [Zero α]
  statement: unop (0 : αᵐᵒᵖ) = 0
  proof: rfl

中文:
引理 unop_zero
  条件: [零 α]
  结论: unop (0 : αᵐᵒᵖ) = 0
  证明: rfl
-/
@[simp] lemma unop_zero [Zero α] : unop (0 : αᵐᵒᵖ) = 0 := rfl

/--
lemma `op_one` / 引理 `op_one`

English:
lemma op_one
  given: [One α]
  statement: op (1 : α) = 1
  proof: rfl

中文:
引理 op_one
  条件: [幺 α]
  结论: op (1 : α) = 1
  证明: rfl
-/
@[to_additive (attr := simp)] lemma op_one [One α] : op (1 : α) = 1 := rfl

/--
lemma `unop_one` / 引理 `unop_one`

English:
lemma unop_one
  given: [One α]
  statement: unop (1 : αᵐᵒᵖ) = 1
  proof: rfl

中文:
引理 unop_one
  条件: [幺 α]
  结论: unop (1 : αᵐᵒᵖ) = 1
  证明: rfl
-/
@[to_additive (attr := simp)] lemma unop_one [One α] : unop (1 : αᵐᵒᵖ) = 1 := rfl

/--
lemma `op_add` / 引理 `op_add`

English:
lemma op_add
  given: [Add α] (x y : α)
  statement: op (x + y) = op x + op y
  proof: rfl

中文:
引理 op_add
  条件: [加法 α] (x y : α)
  结论: op (x + y) = op x + op y
  证明: rfl
-/
@[simp] lemma op_add [Add α] (x y : α) : op (x + y) = op x + op y := rfl

/--
lemma `unop_add` / 引理 `unop_add`

English:
lemma unop_add
  given: [Add α] (x y : αᵐᵒᵖ)
  statement: unop (x + y) = unop x + unop y
  proof: rfl

中文:
引理 unop_add
  条件: [加法 α] (x y : αᵐᵒᵖ)
  结论: unop (x + y) = unop x + unop y
  证明: rfl
-/
@[simp] lemma unop_add [Add α] (x y : αᵐᵒᵖ) : unop (x + y) = unop x + unop y := rfl

/--
lemma `op_neg` / 引理 `op_neg`

English:
lemma op_neg
  given: [Neg α] (x : α)
  statement: op (-x) = -op x
  proof: rfl

中文:
引理 op_neg
  条件: [取负 α] (x : α)
  结论: op (-x) = -op x
  证明: rfl
-/
@[simp] lemma op_neg [Neg α] (x : α) : op (-x) = -op x := rfl

/--
lemma `unop_neg` / 引理 `unop_neg`

English:
lemma unop_neg
  given: [Neg α] (x : αᵐᵒᵖ)
  statement: unop (-x) = -unop x
  proof: rfl

中文:
引理 unop_neg
  条件: [取负 α] (x : αᵐᵒᵖ)
  结论: unop (-x) = -unop x
  证明: rfl
-/
@[simp] lemma unop_neg [Neg α] (x : αᵐᵒᵖ) : unop (-x) = -unop x := rfl

/--
lemma `op_mul` / 引理 `op_mul`

English:
lemma op_mul
  given: [Mul α] (x y : α)
  statement: op (x * y) = op y * op x
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 op_mul
  条件: [乘法 α] (x y : α)
  结论: op (x * y) = op y * op x
  证明: rfl

@[to_additive (attr := simp)]
-/
@[to_additive (attr := simp)] lemma op_mul [Mul α] (x y : α) : op (x * y) = op y * op x := rfl

@[to_additive (attr := simp)]
/--
lemma `unop_mul` / 引理 `unop_mul`

English:
lemma unop_mul
  given: [Mul α] (x y : αᵐᵒᵖ)
  statement: unop (x * y) = unop y * unop x
  proof: rfl

中文:
引理 unop_mul
  条件: [乘法 α] (x y : αᵐᵒᵖ)
  结论: unop (x * y) = unop y * unop x
  证明: rfl
-/
lemma unop_mul [Mul α] (x y : αᵐᵒᵖ) : unop (x * y) = unop y * unop x := rfl

/--
lemma `op_inv` / 引理 `op_inv`

English:
lemma op_inv
  given: [Inv α] (x : α)
  statement: op x⁻¹ = (op x)⁻¹
  proof: rfl

中文:
引理 op_inv
  条件: [取逆 α] (x : α)
  结论: op x⁻¹ = (op x)⁻¹
  证明: rfl
-/
@[to_additive (attr := simp)] lemma op_inv [Inv α] (x : α) : op x⁻¹ = (op x)⁻¹ := rfl

/--
lemma `unop_inv` / 引理 `unop_inv`

English:
lemma unop_inv
  given: [Inv α] (x : αᵐᵒᵖ)
  statement: unop x⁻¹ = (unop x)⁻¹
  proof: rfl

中文:
引理 unop_inv
  条件: [取逆 α] (x : αᵐᵒᵖ)
  结论: unop x⁻¹ = (unop x)⁻¹
  证明: rfl
-/
@[to_additive (attr := simp)] lemma unop_inv [Inv α] (x : αᵐᵒᵖ) : unop x⁻¹ = (unop x)⁻¹ := rfl

/--
lemma `op_sub` / 引理 `op_sub`

English:
lemma op_sub
  given: [Sub α] (x y : α)
  statement: op (x - y) = op x - op y
  proof: rfl

中文:
引理 op_sub
  条件: [减法 α] (x y : α)
  结论: op (x - y) = op x - op y
  证明: rfl
-/
@[simp] lemma op_sub [Sub α] (x y : α) : op (x - y) = op x - op y := rfl

/--
lemma `unop_sub` / 引理 `unop_sub`

English:
lemma unop_sub
  given: [Sub α] (x y : αᵐᵒᵖ)
  statement: unop (x - y) = unop x - unop y
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 unop_sub
  条件: [减法 α] (x y : αᵐᵒᵖ)
  结论: unop (x - y) = unop x - unop y
  证明: rfl

@[to_additive (attr := simp)]
-/
@[simp] lemma unop_sub [Sub α] (x y : αᵐᵒᵖ) : unop (x - y) = unop x - unop y := rfl

@[to_additive (attr := simp)]
/--
lemma `op_smul` / 引理 `op_smul`

English:
lemma op_smul
  given: [SMul α β] (a : α) (b : β)
  statement: op (a • b) = a • op b
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 op_smul
  条件: [标量乘法 α β] (a : α) (b : β)
  结论: op (a • b) = a • op b
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma op_smul [SMul α β] (a : α) (b : β) : op (a • b) = a • op b := rfl

@[to_additive (attr := simp)]
/--
lemma `unop_smul` / 引理 `unop_smul`

English:
lemma unop_smul
  given: [SMul α β] (a : α) (b : βᵐᵒᵖ)
  statement: unop (a • b) = a • unop b
  proof: rfl

@[simp, nolint simpComm]

中文:
引理 unop_smul
  条件: [标量乘法 α β] (a : α) (b : βᵐᵒᵖ)
  结论: unop (a • b) = a • unop b
  证明: rfl

@[simp, nolint simpComm]
-/
lemma unop_smul [SMul α β] (a : α) (b : βᵐᵒᵖ) : unop (a • b) = a • unop b := rfl

@[simp, nolint simpComm]
/--
theorem `unop_eq_zero_iff` / 定理 `unop_eq_zero_iff`

English:
theorem unop_eq_zero_iff
  given: [Zero α] (a : αᵐᵒᵖ)
  statement: a.unop = (0 : α) ↔ a = (0 : αᵐᵒᵖ)
  proof: unop_injective.eq_iff' rfl

@[simp]

中文:
定理 unop_eq_zero_iff
  条件: [零 α] (a : αᵐᵒᵖ)
  结论: a.unop = (0 : α) ↔ a = (0 : αᵐᵒᵖ)
  证明: unop_injective.eq_iff' rfl

@[simp]

Depends on / 依赖: eq_iff, unop_injective, unop_injective.eq_iff
-/
theorem unop_eq_zero_iff [Zero α] (a : αᵐᵒᵖ) : a.unop = (0 : α) ↔ a = (0 : αᵐᵒᵖ) :=
  unop_injective.eq_iff' rfl

@[simp]
/--
theorem `op_eq_zero_iff` / 定理 `op_eq_zero_iff`

English:
theorem op_eq_zero_iff
  given: [Zero α] (a : α)
  statement: op a = (0 : αᵐᵒᵖ) ↔ a = (0 : α)
  proof: op_injective.eq_iff' rfl

中文:
定理 op_eq_zero_iff
  条件: [零 α] (a : α)
  结论: op a = (0 : αᵐᵒᵖ) ↔ a = (0 : α)
  证明: op_injective.eq_iff' rfl

Depends on / 依赖: eq_iff, op_injective, op_injective.eq_iff
-/
theorem op_eq_zero_iff [Zero α] (a : α) : op a = (0 : αᵐᵒᵖ) ↔ a = (0 : α) :=
  op_injective.eq_iff' rfl

/--
theorem `unop_ne_zero_iff` / 定理 `unop_ne_zero_iff`

English:
theorem unop_ne_zero_iff
  given: [Zero α] (a : αᵐᵒᵖ)
  statement: a.unop != (0 : α) ↔ a != (0 : αᵐᵒᵖ)
  proof: not_congr unop_eq_zero_iff a

中文:
定理 unop_ne_zero_iff
  条件: [零 α] (a : αᵐᵒᵖ)
  结论: a.unop != (0 : α) ↔ a != (0 : αᵐᵒᵖ)
  证明: not_congr unop_eq_zero_iff a

Depends on / 依赖: not_congr, unop_eq_zero_iff
-/
theorem unop_ne_zero_iff [Zero α] (a : αᵐᵒᵖ) : a.unop != (0 : α) ↔ a != (0 : αᵐᵒᵖ) :=
not_congr unop_eq_zero_iff a

/--
theorem `op_ne_zero_iff` / 定理 `op_ne_zero_iff`

English:
theorem op_ne_zero_iff
  given: [Zero α] (a : α)
  statement: op a != (0 : αᵐᵒᵖ) ↔ a != (0 : α)
  proof: not_congr op_eq_zero_iff a

@[to_additive (attr := simp, nolint simpComm)]

中文:
定理 op_ne_zero_iff
  条件: [零 α] (a : α)
  结论: op a != (0 : αᵐᵒᵖ) ↔ a != (0 : α)
  证明: not_congr op_eq_zero_iff a

@[to_additive (attr := simp, nolint simpComm)]

Depends on / 依赖: not_congr, op_eq_zero_iff
-/
theorem op_ne_zero_iff [Zero α] (a : α) : op a != (0 : αᵐᵒᵖ) ↔ a != (0 : α) :=
not_congr op_eq_zero_iff a

@[to_additive (attr := simp, nolint simpComm)]
/--
theorem `unop_eq_one_iff` / 定理 `unop_eq_one_iff`

English:
theorem unop_eq_one_iff
  given: [One α] (a : αᵐᵒᵖ)
  statement: a.unop = 1 ↔ a = 1
  proof: unop_injective.eq_iff' rfl

中文:
定理 unop_eq_one_iff
  条件: [幺 α] (a : αᵐᵒᵖ)
  结论: a.unop = 1 ↔ a = 1
  证明: unop_injective.eq_iff' rfl

Depends on / 依赖: eq_iff, unop_injective, unop_injective.eq_iff
-/
theorem unop_eq_one_iff [One α] (a : αᵐᵒᵖ) : a.unop = 1 ↔ a = 1 :=
  unop_injective.eq_iff' rfl

attribute [nolint simpComm] AddOpposite.unop_eq_zero_iff

@[to_additive (attr := simp)]
/--
lemma `op_eq_one_iff` / 引理 `op_eq_one_iff`

English:
lemma op_eq_one_iff
  given: [One α] (a : α)
  statement: op a = 1 ↔ a = 1
  proof: op_injective.eq_iff

中文:
引理 op_eq_one_iff
  条件: [幺 α] (a : α)
  结论: op a = 1 ↔ a = 1
  证明: op_injective.eq_iff

Depends on / 依赖: eq_iff, op_injective, op_injective.eq_iff
-/
lemma op_eq_one_iff [One α] (a : α) : op a = 1 ↔ a = 1 := op_injective.eq_iff

end MulOpposite

namespace AddOpposite

/--
Instance `instOne` / 实例 `instOne`

English:
instance instOne
  signature: [One α]
  body: op 1

中文:
实例 instOne
  签名: [幺 α]
  定义体: op 1
-/
instance instOne [One α] : One αᵃᵒᵖ where one := op 1

/--
lemma `op_one` / 引理 `op_one`

English:
lemma op_one
  given: [One α]
  statement: op (1 : α) = 1
  proof: rfl

中文:
引理 op_one
  条件: [幺 α]
  结论: op (1 : α) = 1
  证明: rfl
-/
@[simp] lemma op_one [One α] : op (1 : α) = 1 := rfl

/--
lemma `unop_one` / 引理 `unop_one`

English:
lemma unop_one
  given: [One α]
  statement: unop 1 = (1 : α)
  proof: rfl

中文:
引理 unop_one
  条件: [幺 α]
  结论: unop 1 = (1 : α)
  证明: rfl
-/
@[simp] lemma unop_one [One α] : unop 1 = (1 : α) := rfl

/--
lemma `op_eq_one_iff` / 引理 `op_eq_one_iff`

English:
lemma op_eq_one_iff
  given: [One α] {a : α}
  statement: op a = 1 ↔ a = 1
  proof: op_injective.eq_iff

中文:
引理 op_eq_one_iff
  条件: [幺 α] {a : α}
  结论: op a = 1 ↔ a = 1
  证明: op_injective.eq_iff
-/
@[simp] lemma op_eq_one_iff [One α] {a : α} : op a = 1 ↔ a = 1 := op_injective.eq_iff

/--
lemma `unop_eq_one_iff` / 引理 `unop_eq_one_iff`

English:
lemma unop_eq_one_iff
  given: [One α] {a : αᵃᵒᵖ}
  statement: unop a = 1 ↔ a = 1
  proof: unop_injective.eq_iff

中文:
引理 unop_eq_one_iff
  条件: [幺 α] {a : αᵃᵒᵖ}
  结论: unop a = 1 ↔ a = 1
  证明: unop_injective.eq_iff
-/
@[simp] lemma unop_eq_one_iff [One α] {a : αᵃᵒᵖ} : unop a = 1 ↔ a = 1 := unop_injective.eq_iff

attribute [nolint simpComm] unop_eq_one_iff

/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: [Mul α]
  body: op (unop a * unop b)

中文:
实例 instMul
  签名: [乘法 α]
  定义体: op (unop a * unop b)
-/
instance instMul [Mul α] : Mul αᵃᵒᵖ where mul a b := op (unop a * unop b)

/--
lemma `op_mul` / 引理 `op_mul`

English:
lemma op_mul
  given: [Mul α] (a b : α)
  statement: op (a * b) = op a * op b
  proof: rfl

中文:
引理 op_mul
  条件: [乘法 α] (a b : α)
  结论: op (a * b) = op a * op b
  证明: rfl
-/
@[simp] lemma op_mul [Mul α] (a b : α) : op (a * b) = op a * op b := rfl

/--
lemma `unop_mul` / 引理 `unop_mul`

English:
lemma unop_mul
  given: [Mul α] (a b : αᵃᵒᵖ)
  statement: unop (a * b) = unop a * unop b
  proof: rfl

中文:
引理 unop_mul
  条件: [乘法 α] (a b : αᵃᵒᵖ)
  结论: unop (a * b) = unop a * unop b
  证明: rfl
-/
@[simp] lemma unop_mul [Mul α] (a b : αᵃᵒᵖ) : unop (a * b) = unop a * unop b := rfl

/--
Instance `instInv` / 实例 `instInv`

English:
instance instInv
  signature: [Inv α]
  body: op (unop a)⁻¹

中文:
实例 instInv
  签名: [取逆 α]
  定义体: op (unop a)⁻¹
-/
instance instInv [Inv α] : Inv αᵃᵒᵖ where inv a := op (unop a)⁻¹

/--
Instance `instInvolutiveInv` / 实例 `instInvolutiveInv`

English:
instance instInvolutiveInv
  signature: [InvolutiveInv α]
  body: unop_injective inv_inv _

中文:
实例 instInvolutiveInv
  签名: [InvolutiveInv α]
  定义体: unop_injective inv_inv _

Depends on / 依赖: inv_inv, unop_injective
-/
instance instInvolutiveInv [InvolutiveInv α] : InvolutiveInv αᵃᵒᵖ where
inv_inv _ := unop_injective inv_inv _

/--
lemma `op_inv` / 引理 `op_inv`

English:
lemma op_inv
  given: [Inv α] (a : α)
  statement: op a⁻¹ = (op a)⁻¹
  proof: rfl

中文:
引理 op_inv
  条件: [取逆 α] (a : α)
  结论: op a⁻¹ = (op a)⁻¹
  证明: rfl
-/
@[simp] lemma op_inv [Inv α] (a : α) : op a⁻¹ = (op a)⁻¹ := rfl

/--
lemma `unop_inv` / 引理 `unop_inv`

English:
lemma unop_inv
  given: [Inv α] (a : αᵃᵒᵖ)
  statement: unop a⁻¹ = (unop a)⁻¹
  proof: rfl

中文:
引理 unop_inv
  条件: [取逆 α] (a : αᵃᵒᵖ)
  结论: unop a⁻¹ = (unop a)⁻¹
  证明: rfl
-/
@[simp] lemma unop_inv [Inv α] (a : αᵃᵒᵖ) : unop a⁻¹ = (unop a)⁻¹ := rfl

/--
Instance `instDiv` / 实例 `instDiv`

English:
instance instDiv
  signature: [Div α]
  body: op (unop a / unop b)

中文:
实例 instDiv
  签名: [除法 α]
  定义体: op (unop a / unop b)
-/
instance instDiv [Div α] : Div αᵃᵒᵖ where div a b := op (unop a / unop b)

/--
lemma `op_div` / 引理 `op_div`

English:
lemma op_div
  given: [Div α] (a b : α)
  statement: op (a / b) = op a / op b
  proof: rfl

中文:
引理 op_div
  条件: [除法 α] (a b : α)
  结论: op (a / b) = op a / op b
  证明: rfl
-/
@[simp] lemma op_div [Div α] (a b : α) : op (a / b) = op a / op b := rfl

/--
lemma `unop_div` / 引理 `unop_div`

English:
lemma unop_div
  given: [Div α] (a b : αᵃᵒᵖ)
  statement: unop (a / b) = unop a / unop b
  proof: rfl

中文:
引理 unop_div
  条件: [除法 α] (a b : αᵃᵒᵖ)
  结论: unop (a / b) = unop a / unop b
  证明: rfl
-/
@[simp] lemma unop_div [Div α] (a b : αᵃᵒᵖ) : unop (a / b) = unop a / unop b := rfl

end AddOpposite
