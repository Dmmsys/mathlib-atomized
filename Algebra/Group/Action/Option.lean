/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Faithful

/-!
# Option instances for additive and multiplicative actions

This file defines instances for additive and multiplicative actions on `Option` type. Scalar
multiplication is defined by `a • some b = some (a • b)` and `a • none = none`.

## See also

* `Mathlib/Algebra/Group/Action/Pi.lean`
* `Mathlib/Algebra/Group/Action/Sigma.lean`
* `Mathlib/Algebra/Group/Action/Sum.lean`
-/

@[expose] public section

assert_not_exists MonoidWithZero

variable {M N α : Type*}

namespace Option

section SMul

variable [SMul M α] [SMul N α] (a : M) (b : α) (x : Option α)

@[to_additive Option.VAdd]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul M (Option α)
  body: ⟨fun a => Option.map (a • ·)⟩

@[to_additive]

中文:
实例 :
  签名: SMul M (Option α)
  定义体: ⟨fun a => Option.map (a • ·)⟩

@[to_additive]

Depends on / 依赖: Option.map
-/
instance : SMul M (Option α) :=
⟨fun a => Option.map (a • ·)⟩

@[to_additive]
/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  statement: a • x = x.map (a • ·)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 smul_def
  结论: a • x = x.map (a • ·)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem smul_def : a • x = x.map (a • ·) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `smul_none` / 定理 `smul_none`

English:
theorem smul_none
  statement: a • (none : Option α) = none
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 smul_none
  结论: a • (none : Option α) = none
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem smul_none : a • (none : Option α) = none :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `smul_some` / 定理 `smul_some`

English:
theorem smul_some
  statement: a • some b = some (a • b)
  proof: rfl

@[to_additive]

中文:
定理 smul_some
  结论: a • some b = some (a • b)
  证明: rfl

@[to_additive]
-/
theorem smul_some : a • some b = some (a • b) :=
  rfl

@[to_additive]
/--
Instance `instIsScalarTowerOfSMul` / 实例 `instIsScalarTowerOfSMul`

English:
instance instIsScalarTowerOfSMul
  signature: [SMul M N] [IsScalarTower M N α]
  body: ⟨fun a b x => by
    cases x
    exacts [rfl, congr_arg some (smul_assoc _ _ _)]⟩

@[to_additive]

中文:
实例 instIsScalarTowerOfSMul
  签名: [SMul M N] [IsScalarTower M N α]
  定义体: ⟨fun a b x => by
    cases x
    exacts [rfl, congr_arg some (smul_assoc _ _ _)]⟩

@[to_additive]

Depends on / 依赖: congr_arg, exacts, smul_assoc
-/
instance instIsScalarTowerOfSMul [SMul M N] [IsScalarTower M N α] : IsScalarTower M N (Option α) :=
  ⟨fun a b x => by
    cases x
    exacts [rfl, congr_arg some (smul_assoc _ _ _)]⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMulCommClass
  signature: M N α] : SMulCommClass M N (Option α)
  body: ⟨fun _ _ => Function.Commute.option_map smul_comm _ _⟩

@[to_additive]

中文:
实例 [SMulCommClass
  签名: M N α] : SMulCommClass M N (Option α)
  定义体: ⟨fun _ _ => Function.Commute.option_map smul_comm _ _⟩

@[to_additive]

Depends on / 依赖: Commute, Function, Function.Commute.option_map, option_map, smul_comm
-/
instance [SMulCommClass M N α] : SMulCommClass M N (Option α) :=
⟨fun _ _ => Function.Commute.option_map smul_comm _ _⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: Mᵐᵒᵖ α] [IsCentralScalar M α] : IsCentralScalar M (Option α)
  body: ⟨fun a x => by
    cases x
    exacts [rfl, congr_arg some (op_smul_eq_smul _ _)]⟩

@[to_additive]

中文:
实例 [SMul
  签名: Mᵐᵒᵖ α] [IsCentralScalar M α] : IsCentralScalar M (Option α)
  定义体: ⟨fun a x => by
    cases x
    exacts [rfl, congr_arg some (op_smul_eq_smul _ _)]⟩

@[to_additive]

Depends on / 依赖: congr_arg, exacts, op_smul_eq_smul
-/
instance [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] : IsCentralScalar M (Option α) :=
  ⟨fun a x => by
    cases x
    exacts [rfl, congr_arg some (op_smul_eq_smul _ _)]⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FaithfulSMul
  signature: M α] : FaithfulSMul M (Option α)
  body: ⟨fun h => eq_of_smul_eq_smul fun b : α => by injection h (some b)⟩

中文:
实例 [FaithfulSMul
  签名: M α] : FaithfulSMul M (Option α)
  定义体: ⟨fun h => eq_of_smul_eq_smul fun b : α => by injection h (some b)⟩

Depends on / 依赖: eq_of_smul_eq_smul, injection
-/
instance [FaithfulSMul M α] : FaithfulSMul M (Option α) :=
  ⟨fun h => eq_of_smul_eq_smul fun b : α => by injection h (some b)⟩

end SMul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: M] [MulAction M α] :
  body: by
    cases b
    exacts [rfl, congr_arg some (one_smul _ _)]
  mul_smul a₁ a₂ b := by
    cases b
    exacts [rfl, congr_arg some (mul_smul _ _ _)]

中文:
实例 [Monoid
  签名: M] [MulAction M α] :
  定义体: by
    cases b
    exacts [rfl, congr_arg some (one_smul _ _)]
  mul_smul a₁ a₂ b := by
    cases b
    exacts [rfl, congr_arg some (mul_smul _ _ _)]

Depends on / 依赖: congr_arg, exacts, mul_smul, one_smul
-/
instance [Monoid M] [MulAction M α] :
    MulAction M (Option α) where
  one_smul b := by
    cases b
    exacts [rfl, congr_arg some (one_smul _ _)]
  mul_smul a₁ a₂ b := by
    cases b
    exacts [rfl, congr_arg some (mul_smul _ _ _)]

end Option
