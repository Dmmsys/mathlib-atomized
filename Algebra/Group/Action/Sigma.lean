/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Faithful
public import Mathlib.Data.Sigma.Basic

/-!
# Sigma instances for additive and multiplicative actions

This file defines instances for arbitrary sum of additive and multiplicative actions.

## See also

* `Mathlib/Algebra/Group/Action/Option.lean`
* `Mathlib/Algebra/Group/Action/Pi.lean`
* `Mathlib/Algebra/Group/Action/Prod.lean`
* `Mathlib/Algebra/Group/Action/Sum.lean`
-/

@[expose] public section

assert_not_exists MonoidWithZero


variable {ι : Type*} {M N : Type*} {α : ι -> Type*}

namespace Sigma

section SMul

variable [forall i, SMul M (α i)] [forall i, SMul N (α i)] (a : M) (i : ι) (b : α i) (x : Σ i, α i)

@[to_additive Sigma.VAdd]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul M (Σ i, α i)
  body: ⟨fun a => (Sigma.map id) fun _ => (a • ·)⟩

@[to_additive]

中文:
实例 :
  签名: SMul M (Σ i, α i)
  定义体: ⟨fun a => (Sigma.map id) fun _ => (a • ·)⟩

@[to_additive]

Depends on / 依赖: Sigma.map
-/
instance : SMul M (Σ i, α i) :=
  ⟨fun a => (Sigma.map id) fun _ => (a • ·)⟩

@[to_additive]
/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  statement: a • x = x.map id fun _ => (a • ·)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 smul_def
  结论: a • x = x.map id fun _ => (a • ·)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem smul_def : a • x = x.map id fun _ => (a • ·) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `smul_mk` / 定理 `smul_mk`

English:
theorem smul_mk
  statement: a • mk i b = ⟨i, a • b⟩
  proof: rfl

@[to_additive]

中文:
定理 smul_mk
  结论: a • mk i b = ⟨i, a • b⟩
  证明: rfl

@[to_additive]
-/
theorem smul_mk : a • mk i b = ⟨i, a • b⟩ :=
  rfl

@[to_additive]
/--
Instance `instIsScalarTowerOfSMul` / 实例 `instIsScalarTowerOfSMul`

English:
instance instIsScalarTowerOfSMul
  signature: [SMul M N] [forall i, IsScalarTower M N (α i)]
  body: ⟨fun a b x => by
    cases x
    rw [smul_mk]; rw [smul_mk]; rw [smul_mk]; rw [smul_assoc]⟩

@[to_additive]

中文:
实例 instIsScalarTowerOfSMul
  签名: [SMul M N] [对任意 i, IsScalarTower M N (α i)]
  定义体: ⟨fun a b x => by
    cases x
    rw [smul_mk]; rw [smul_mk]; rw [smul_mk]; rw [smul_assoc]⟩

@[to_additive]

Depends on / 依赖: smul_assoc, smul_mk
-/
instance instIsScalarTowerOfSMul [SMul M N] [forall i, IsScalarTower M N (α i)] :
    IsScalarTower M N (Σ i, α i) :=
  ⟨fun a b x => by
    cases x
    rw [smul_mk]; rw [smul_mk]; rw [smul_mk]; rw [smul_assoc]⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, SMulCommClass M N (α i)] : SMulCommClass M N (Σ i, α i)
  body: ⟨fun a b x => by
    cases x
    rw [smul_mk]; rw [smul_mk]; rw [smul_mk]; rw [smul_mk]; rw [smul_comm]⟩

@[to_additive]

中文:
实例 [forall
  签名: i, SMulCommClass M N (α i)] : SMulCommClass M N (Σ i, α i)
  定义体: ⟨fun a b x => by
    cases x
    rw [smul_mk]; rw [smul_mk]; rw [smul_mk]; rw [smul_mk]; rw [smul_comm]⟩

@[to_additive]

Depends on / 依赖: smul_comm, smul_mk
-/
instance [forall i, SMulCommClass M N (α i)] : SMulCommClass M N (Σ i, α i) :=
  ⟨fun a b x => by
    cases x
    rw [smul_mk]; rw [smul_mk]; rw [smul_mk]; rw [smul_mk]; rw [smul_comm]⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, SMul Mᵐᵒᵖ (α i)] [forall i, IsCentralScalar M (α i)] : IsCentralScalar M (Σ i, α i)
  body: ⟨fun a x => by
    cases x
    rw [smul_mk]; rw [smul_mk]; rw [op_smul_eq_smul]⟩

中文:
实例 [forall
  签名: i, SMul Mᵐᵒᵖ (α i)] [对任意 i, IsCentralScalar M (α i)] : IsCentralScalar M (Σ i, α i)
  定义体: ⟨fun a x => by
    cases x
    rw [smul_mk]; rw [smul_mk]; rw [op_smul_eq_smul]⟩

Depends on / 依赖: op_smul_eq_smul, smul_mk
-/
instance [forall i, SMul Mᵐᵒᵖ (α i)] [forall i, IsCentralScalar M (α i)] : IsCentralScalar M (Σ i, α i) :=
  ⟨fun a x => by
    cases x
    rw [smul_mk]; rw [smul_mk]; rw [op_smul_eq_smul]⟩

/-- This is not an instance because `i` becomes a metavariable. -/
@[to_additive /-- This is not an instance because `i` becomes a metavariable. -/]
/--
theorem `FaithfulSMul'` / 定理 `FaithfulSMul'`

English:
theorem FaithfulSMul'
  given: [FaithfulSMul M (α i)]
  statement: FaithfulSMul M (Σ i, α i)
  proof: ⟨fun h => eq_of_smul_eq_smul fun a : α i => heq_iff_eq.1 (Sigma.ext_iff.1 <| h <| mk i a).2⟩

@[to_additive]

中文:
定理 FaithfulSMul'
  条件: [FaithfulSMul M (α i)]
  结论: FaithfulSMul M (Σ i, α i)
  证明: ⟨fun h => eq_of_smul_eq_smul fun a : α i => heq_iff_eq.1 (Sigma.ext_iff.1 <| h <| mk i a).2⟩

@[to_additive]
-/
protected theorem FaithfulSMul' [FaithfulSMul M (α i)] : FaithfulSMul M (Σ i, α i) :=
  ⟨fun h => eq_of_smul_eq_smul fun a : α i => heq_iff_eq.1 (Sigma.ext_iff.1 <| h <| mk i a).2⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: ι] [forall i, FaithfulSMul M (α i)] : FaithfulSMul M (Σ i, α i)
  body: (Nonempty.elim ‹_›) fun i => Sigma.FaithfulSMul' i

中文:
实例 [Nonempty
  签名: ι] [对任意 i, FaithfulSMul M (α i)] : FaithfulSMul M (Σ i, α i)
  定义体: (Nonempty.elim ‹_›) fun i => Sigma.FaithfulSMul' i

Depends on / 依赖: FaithfulSMul, Nonempty, Nonempty.elim, Sigma.FaithfulSMul
-/
instance [Nonempty ι] [forall i, FaithfulSMul M (α i)] : FaithfulSMul M (Σ i, α i) :=
  (Nonempty.elim ‹_›) fun i => Sigma.FaithfulSMul' i

end SMul

@[to_additive]
instance {m : Monoid M} [forall i, MulAction M (α i)] :
    MulAction M (Σ i, α i) where
  mul_smul a b x := by
    cases x
    rw [smul_mk]; rw [smul_mk]; rw [smul_mk]; rw [mul_smul]
  one_smul x := by
    cases x
    rw [smul_mk]; rw [one_smul]

end Sigma
