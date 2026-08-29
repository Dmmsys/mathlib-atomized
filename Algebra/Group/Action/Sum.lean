/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Faithful

/-!
# Sum instances for additive and multiplicative actions

This file defines instances for additive and multiplicative actions on the binary `Sum` type.

## See also

* `Mathlib/Algebra/Group/Action/Option.lean`
* `Mathlib/Algebra/Group/Action/Pi.lean`
* `Mathlib/Algebra/Group/Action/Prod.lean`
* `Mathlib/Algebra/Group/Action/Sigma.lean`
-/

@[expose] public section

assert_not_exists MonoidWithZero

variable {M N α β : Type*}

namespace Sum

section SMul

variable [SMul M α] [SMul M β] [SMul N α] [SMul N β] (a : M) (b : α) (c : β)
  (x : α oplus β)

@[to_additive]
/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: : SMul M (α oplus β)
  body: ⟨fun a => Sum.map (a • ·) (a • ·)⟩

@[to_additive]

中文:
实例 instSMul
  签名: : SMul M (α oplus β)
  定义体: ⟨fun a => Sum.map (a • ·) (a • ·)⟩

@[to_additive]

Depends on / 依赖: Sum.map
-/
instance instSMul : SMul M (α oplus β) :=
  ⟨fun a => Sum.map (a • ·) (a • ·)⟩

@[to_additive]
/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  statement: a • x = x.map (a • ·) (a • ·)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 smul_def
  结论: a • x = x.map (a • ·) (a • ·)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem smul_def : a • x = x.map (a • ·) (a • ·) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `smul_inl` / 定理 `smul_inl`

English:
theorem smul_inl
  statement: a • (inl b : α oplus β) = inl (a • b)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 smul_inl
  结论: a • (inl b : α oplus β) = inl (a • b)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem smul_inl : a • (inl b : α oplus β) = inl (a • b) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `smul_inr` / 定理 `smul_inr`

English:
theorem smul_inr
  statement: a • (inr c : α oplus β) = inr (a • c)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 smul_inr
  结论: a • (inr c : α oplus β) = inr (a • c)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem smul_inr : a • (inr c : α oplus β) = inr (a • c) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `smul_swap` / 定理 `smul_swap`

English:
theorem smul_swap
  statement: (a • x).swap = a • x.swap
  proof: by cases x <;> rfl

中文:
定理 smul_swap
  结论: (a • x).swap = a • x.swap
  证明: by cases x <;> rfl
-/
theorem smul_swap : (a • x).swap = a • x.swap := by cases x <;> rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M N] [IsScalarTower M N α] [IsScalarTower M N β] : IsScalarTower M N (α oplus β)
  body: ⟨fun a b x => by
    cases x
    exacts [congr_arg inl (smul_assoc _ _ _), congr_arg inr (smul_assoc _ _ _)]⟩

@[to_additive]

中文:
实例 [SMul
  签名: M N] [IsScalarTower M N α] [IsScalarTower M N β] : IsScalarTower M N (α oplus β)
  定义体: ⟨fun a b x => by
    cases x
    exacts [congr_arg inl (smul_assoc _ _ _), congr_arg inr (smul_assoc _ _ _)]⟩

@[to_additive]

Depends on / 依赖: congr_arg, exacts, smul_assoc
-/
instance [SMul M N] [IsScalarTower M N α] [IsScalarTower M N β] : IsScalarTower M N (α oplus β) :=
  ⟨fun a b x => by
    cases x
    exacts [congr_arg inl (smul_assoc _ _ _), congr_arg inr (smul_assoc _ _ _)]⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMulCommClass
  signature: M N α] [SMulCommClass M N β] : SMulCommClass M N (α oplus β)
  body: ⟨fun a b x => by
    cases x
    exacts [congr_arg inl (smul_comm _ _ _), congr_arg inr (smul_comm _ _ _)]⟩

@[to_additive]

中文:
实例 [SMulCommClass
  签名: M N α] [SMulCommClass M N β] : SMulCommClass M N (α oplus β)
  定义体: ⟨fun a b x => by
    cases x
    exacts [congr_arg inl (smul_comm _ _ _), congr_arg inr (smul_comm _ _ _)]⟩

@[to_additive]

Depends on / 依赖: congr_arg, exacts, smul_comm
-/
instance [SMulCommClass M N α] [SMulCommClass M N β] : SMulCommClass M N (α oplus β) :=
  ⟨fun a b x => by
    cases x
    exacts [congr_arg inl (smul_comm _ _ _), congr_arg inr (smul_comm _ _ _)]⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: Mᵐᵒᵖ α] [SMul Mᵐᵒᵖ β] [IsCentralScalar M α] [IsCentralScalar M β] :
  body: ⟨fun a x => by
    cases x
    exacts [congr_arg inl (op_smul_eq_smul _ _), congr_arg inr (op_smul_eq_smul _ _)]⟩

@[to_additive]

中文:
实例 [SMul
  签名: Mᵐᵒᵖ α] [SMul Mᵐᵒᵖ β] [IsCentralScalar M α] [IsCentralScalar M β] :
  定义体: ⟨fun a x => by
    cases x
    exacts [congr_arg inl (op_smul_eq_smul _ _), congr_arg inr (op_smul_eq_smul _ _)]⟩

@[to_additive]

Depends on / 依赖: congr_arg, exacts, op_smul_eq_smul
-/
instance [SMul Mᵐᵒᵖ α] [SMul Mᵐᵒᵖ β] [IsCentralScalar M α] [IsCentralScalar M β] :
    IsCentralScalar M (α oplus β) :=
  ⟨fun a x => by
    cases x
    exacts [congr_arg inl (op_smul_eq_smul _ _), congr_arg inr (op_smul_eq_smul _ _)]⟩

@[to_additive]
/--
Instance `FaithfulSMulLeft` / 实例 `FaithfulSMulLeft`

English:
instance FaithfulSMulLeft
  signature: [FaithfulSMul M α]
  body: ⟨fun h => eq_of_smul_eq_smul fun a : α => by injection h (inl a)⟩

@[to_additive]

中文:
实例 FaithfulSMulLeft
  签名: [FaithfulSMul M α]
  定义体: ⟨fun h => eq_of_smul_eq_smul fun a : α => by injection h (inl a)⟩

@[to_additive]

Depends on / 依赖: eq_of_smul_eq_smul, injection
-/
instance FaithfulSMulLeft [FaithfulSMul M α] : FaithfulSMul M (α oplus β) :=
  ⟨fun h => eq_of_smul_eq_smul fun a : α => by injection h (inl a)⟩

@[to_additive]
/--
Instance `FaithfulSMulRight` / 实例 `FaithfulSMulRight`

English:
instance FaithfulSMulRight
  signature: [FaithfulSMul M β]
  body: ⟨fun h => eq_of_smul_eq_smul fun b : β => by injection h (inr b)⟩

中文:
实例 FaithfulSMulRight
  签名: [FaithfulSMul M β]
  定义体: ⟨fun h => eq_of_smul_eq_smul fun b : β => by injection h (inr b)⟩

Depends on / 依赖: eq_of_smul_eq_smul, injection
-/
instance FaithfulSMulRight [FaithfulSMul M β] : FaithfulSMul M (α oplus β) :=
  ⟨fun h => eq_of_smul_eq_smul fun b : β => by injection h (inr b)⟩

end SMul

@[to_additive]
instance {m : Monoid M} [MulAction M α] [MulAction M β] :
    MulAction M (α oplus β) where
  mul_smul a b x := by
    cases x
    exacts [congr_arg inl (mul_smul _ _ _), congr_arg inr (mul_smul _ _ _)]
  one_smul x := by
    cases x
    exacts [congr_arg inl (one_smul _ _), congr_arg inr (one_smul _ _)]

end Sum
