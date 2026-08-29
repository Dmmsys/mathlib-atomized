/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Finite.Prod

/-!
# Finiteness of `DFunLike` types

We show a type `F` with a `DFunLike F α β` is finite if both `α` and `β` are finite.
This corresponds to the following two pairs of declarations:

* `DFunLike.fintype` is a definition stating all `DFunLike`s are finite if their domain and
  codomain are.
* `DFunLike.finite` is a lemma stating all `DFunLike`s are finite if their domain and
  codomain are.
* `FunLike.fintype` is a non-dependent version of `DFunLike.fintype` and
* `FunLike.finite` is a non-dependent version of `DFunLike.finite`, because dependent instances
  are harder to infer.

You can use these to produce instances for specific `DFunLike` types.
(Although there might be options for `Fintype` instances with better definitional behaviour.)
They can't be instances themselves since they can cause loops.
-/

@[expose] public section

-- `Type` is a reserved word, switched to `Type'`
section Type'

variable (F G : Type*) {α γ : Type*} {β : α -> Type*} [DFunLike F α β] [FunLike G α γ]

/-- All `DFunLike`s are finite if their domain and codomain are.

This is not an instance because specific `DFunLike` types might have a better-suited definition.

See also `DFunLike.finite`.
-/
@[instance_reducible]
/--
Definition of `DFunLike.fintype` / `DFunLike.fintype` 的定义

English:
definition DFunLike.fintype
  signature: [DecidableEq α] [Fintype α] [forall i, Fintype (β i)]
  body: Fintype.ofInjective _ DFunLike.coe_injective

中文:
定义 依赖函数状.fintype
  签名: [DecidableEq α] [有限类型 α] [对任意 i, 有限类型 (β i)]
  定义体: Fintype.ofInjective _ DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Fintype, Fintype.ofInjective, coe_injective, ofInjective
-/
noncomputable def DFunLike.fintype [DecidableEq α] [Fintype α] [forall i, Fintype (β i)] : Fintype F :=
  Fintype.ofInjective _ DFunLike.coe_injective

/-- All `FunLike`s are finite if their domain and codomain are.

Non-dependent version of `DFunLike.fintype` that might be easier to infer.
This is not an instance because specific `FunLike` types might have a better-suited definition.
-/
@[instance_reducible]
/--
Definition of `FunLike.fintype` / `FunLike.fintype` 的定义

English:
definition FunLike.fintype
  signature: [DecidableEq α] [Fintype α] [Fintype γ]
  body: DFunLike.fintype G

中文:
定义 函数状.fintype
  签名: [DecidableEq α] [有限类型 α] [有限类型 γ]
  定义体: DFunLike.fintype G

Depends on / 依赖: DFunLike, DFunLike.fintype, fintype
-/
noncomputable def FunLike.fintype [DecidableEq α] [Fintype α] [Fintype γ] : Fintype G :=
  DFunLike.fintype G

end Type'

-- `Sort` is a reserved word, switched to `Sort'`
section Sort'

variable (F G : Sort*) {α γ : Sort*} {β : α -> Sort*} [DFunLike F α β] [FunLike G α γ]

/--
theorem `DFunLike.finite` / 定理 `DFunLike.finite`

English:
theorem DFunLike.finite
  given: [Finite α] [forall i, Finite (β i)]
  statement: Finite F
  proof: Finite.of_injective _ DFunLike.coe_injective

中文:
定理 依赖函数状.finite
  条件: [有限 α] [对任意 i, 有限 (β i)]
  结论: 有限 F
  证明: Finite.of_injective _ DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Finite, Finite.of_injective, coe_injective, h.symm, of_injective
-/
theorem DFunLike.finite [Finite α] [forall i, Finite (β i)] : Finite F :=
  Finite.of_injective _ DFunLike.coe_injective

/--
theorem `FunLike.finite` / 定理 `FunLike.finite`

English:
theorem FunLike.finite
  given: [Finite α] [Finite γ]
  statement: Finite G
  proof: DFunLike.finite G

中文:
定理 函数状.finite
  条件: [有限 α] [有限 γ]
  结论: 有限 G
  证明: DFunLike.finite G

Depends on / 依赖: DFunLike, DFunLike.finite, finite
-/
theorem FunLike.finite [Finite α] [Finite γ] : Finite G :=
  DFunLike.finite G

end Sort'

-- See note [lower instance priority]
instance (priority := 100) FunLike.toDecidableEq {F α β : Type*}
    [DecidableEq β] [Fintype α] [FunLike F α β] : DecidableEq F :=
  fun a b => decidable_of_iff ((a : α -> β) = b) DFunLike.coe_injective.eq_iff
