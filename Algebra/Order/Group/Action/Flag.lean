/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Order.Group.Action.End
public import Mathlib.Order.Preorder.Chain

/-!
# Action on flags

Order isomorphisms act on flags.
-/

public section

open scoped Pointwise

variable {α : Type*}

namespace Flag
variable [Preorder α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul (α ≃o α) (Flag α)
  body: map e

@[simp, norm_cast]

中文:
实例 :
  签名: 标量乘法 (α ≃o α) (旗 α)
  定义体: map e

@[simp, norm_cast]
-/
instance : SMul (α ≃o α) (Flag α) where smul e := map e

@[simp, norm_cast]
/--
lemma `coe_smul` / 引理 `coe_smul`

English:
lemma coe_smul
  given: (e : α ≃o α) (s : Flag α)
  statement: (↑(e • s) : Set α) = e • s
  proof: rfl

中文:
引理 coe_smul
  条件: (e : α ≃o α) (s : 旗 α)
  结论: (↑(e • s) : 集合 α) = e • s
  证明: rfl
-/
lemma coe_smul (e : α ≃o α) (s : Flag α) : (↑(e • s) : Set α) = e • s := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction (α ≃o α) (Flag α)
  body: SetLike.coe_injective.mulAction _ coe_smul

中文:
实例 :
  签名: 乘法作用 (α ≃o α) (旗 α)
  定义体: SetLike.coe_injective.mulAction _ coe_smul

Depends on / 依赖: SetLike, SetLike.coe_injective.mulAction, coe_injective, coe_smul, mulAction
-/
instance : MulAction (α ≃o α) (Flag α) := SetLike.coe_injective.mulAction _ coe_smul

end Flag
