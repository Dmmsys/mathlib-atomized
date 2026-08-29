/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Action.Faithful
public import Mathlib.Algebra.Group.Action.Hom
public import Mathlib.Algebra.Group.Prod

/-!
# Prod instances for additive and multiplicative actions

This file defines instances for binary product of additive and multiplicative actions and provides
scalar multiplication as a homomorphism from `α × β` to `β`.

## Main declarations

* `smulMulHom`/`smulMonoidHom`: Scalar multiplication bundled as a multiplicative/monoid
  homomorphism.

## See also

* `Mathlib/Algebra/Group/Action/Option.lean`
* `Mathlib/Algebra/Group/Action/Pi.lean`
* `Mathlib/Algebra/Group/Action/Sigma.lean`
* `Mathlib/Algebra/Group/Action/Sum.lean`

## Porting notes

The `to_additive` attribute can be used to generate both the `smul` and `vadd` lemmas
from the corresponding `pow` lemmas, as explained on zulip here:
https://leanprover.zulipchat.com/#narrow/near/316087838

This was not done as part of the port in order to stay as close as possible to the mathlib3 code.
-/

@[expose] public section

assert_not_exists MonoidWithZero

variable {M N P E α β : Type*}

namespace Prod

section
variable [SMul M α] [SMul M β] [SMul N α] [SMul N β] (a : M) (x : α × β)

@[to_additive]
/--
Instance `isScalarTower` / 实例 `isScalarTower`

English:
instance isScalarTower
  signature: [SMul M N] [IsScalarTower M N α] [IsScalarTower M N β]
  body: by ext <;> exact smul_assoc ..

@[to_additive]

中文:
实例 isScalarTower
  签名: [SMul M N] [IsScalarTower M N α] [IsScalarTower M N β]
  定义体: by ext <;> exact smul_assoc ..

@[to_additive]

Depends on / 依赖: smul_assoc
-/
instance isScalarTower [SMul M N] [IsScalarTower M N α] [IsScalarTower M N β] :
    IsScalarTower M N (α × β) where
  smul_assoc _ _ _ := by ext <;> exact smul_assoc ..

@[to_additive]
/--
Instance `smulCommClass` / 实例 `smulCommClass`

English:
instance smulCommClass
  signature: [SMulCommClass M N α] [SMulCommClass M N β]
  body: by ext <;> exact smul_comm ..

@[to_additive]

中文:
实例 smulCommClass
  签名: [SMulCommClass M N α] [SMulCommClass M N β]
  定义体: by ext <;> exact smul_comm ..

@[to_additive]

Depends on / 依赖: smul_comm
-/
instance smulCommClass [SMulCommClass M N α] [SMulCommClass M N β] : SMulCommClass M N (α × β) where
  smul_comm _ _ _ := by ext <;> exact smul_comm ..

@[to_additive]
/--
Instance `isCentralScalar` / 实例 `isCentralScalar`

English:
instance isCentralScalar
  signature: [SMul Mᵐᵒᵖ α] [SMul Mᵐᵒᵖ β] [IsCentralScalar M α] [IsCentralScalar M β]
  body: Prod.ext (op_smul_eq_smul _ _) (op_smul_eq_smul _ _)

@[to_additive]

中文:
实例 isCentralScalar
  签名: [SMul Mᵐᵒᵖ α] [SMul Mᵐᵒᵖ β] [IsCentralScalar M α] [IsCentralScalar M β]
  定义体: Prod.ext (op_smul_eq_smul _ _) (op_smul_eq_smul _ _)

@[to_additive]

Depends on / 依赖: Prod.ext, op_smul_eq_smul
-/
instance isCentralScalar [SMul Mᵐᵒᵖ α] [SMul Mᵐᵒᵖ β] [IsCentralScalar M α] [IsCentralScalar M β] :
    IsCentralScalar M (α × β) where
  op_smul_eq_smul _ _ := Prod.ext (op_smul_eq_smul _ _) (op_smul_eq_smul _ _)

@[to_additive]
/--
Instance `faithfulSMulLeft` / 实例 `faithfulSMulLeft`

English:
instance faithfulSMulLeft
  signature: [FaithfulSMul M α] [Nonempty β]
  body: let ⟨b⟩ := ‹Nonempty β›
    eq_of_smul_eq_smul fun a : α => by injection h (a, b)

@[to_additive]

中文:
实例 faithfulSMulLeft
  签名: [FaithfulSMul M α] [Nonempty β]
  定义体: let ⟨b⟩ := ‹Nonempty β›
    eq_of_smul_eq_smul fun a : α => by injection h (a, b)

@[to_additive]

Depends on / 依赖: Nonempty, eq_of_smul_eq_smul, injection
-/
instance faithfulSMulLeft [FaithfulSMul M α] [Nonempty β] : FaithfulSMul M (α × β) where
  eq_of_smul_eq_smul h :=
    let ⟨b⟩ := ‹Nonempty β›
    eq_of_smul_eq_smul fun a : α => by injection h (a, b)

@[to_additive]
/--
Instance `faithfulSMulRight` / 实例 `faithfulSMulRight`

English:
instance faithfulSMulRight
  signature: [Nonempty α] [FaithfulSMul M β]
  body: let ⟨a⟩ := ‹Nonempty α›
    eq_of_smul_eq_smul fun b : β => by injection h (a, b)

中文:
实例 faithfulSMulRight
  签名: [Nonempty α] [FaithfulSMul M β]
  定义体: let ⟨a⟩ := ‹Nonempty α›
    eq_of_smul_eq_smul fun b : β => by injection h (a, b)

Depends on / 依赖: Nonempty, eq_of_smul_eq_smul, injection
-/
instance faithfulSMulRight [Nonempty α] [FaithfulSMul M β] : FaithfulSMul M (α × β) where
  eq_of_smul_eq_smul h :=
    let ⟨a⟩ := ‹Nonempty α›
    eq_of_smul_eq_smul fun b : β => by injection h (a, b)

end

@[to_additive]
/--
Instance `smulCommClassBoth` / 实例 `smulCommClassBoth`

English:
instance smulCommClassBoth
  signature: [Mul N] [Mul P] [SMul M N] [SMul M P] [SMulCommClass M N N]
  body: by simp [smul_def, mul_def, mul_smul_comm]

中文:
实例 smulCommClassBoth
  签名: [Mul N] [Mul P] [SMul M N] [SMul M P] [SMulCommClass M N N]
  定义体: by simp [smul_def, mul_def, mul_smul_comm]

Depends on / 依赖: mul_def, mul_smul_comm, smul_def
-/
instance smulCommClassBoth [Mul N] [Mul P] [SMul M N] [SMul M P] [SMulCommClass M N N]
    [SMulCommClass M P P] : SMulCommClass M (N × P) (N × P) where
  smul_comm c x y := by simp [smul_def, mul_def, mul_smul_comm]

/--
Instance `isScalarTowerBoth` / 实例 `isScalarTowerBoth`

English:
instance isScalarTowerBoth
  signature: [Mul N] [Mul P] [SMul M N] [SMul M P] [IsScalarTower M N N]
  body: by simp [smul_def, mul_def, smul_mul_assoc]

@[to_additive]

中文:
实例 isScalarTowerBoth
  签名: [Mul N] [Mul P] [SMul M N] [SMul M P] [IsScalarTower M N N]
  定义体: by simp [smul_def, mul_def, smul_mul_assoc]

@[to_additive]

Depends on / 依赖: mul_def, smul_def, smul_mul_assoc
-/
instance isScalarTowerBoth [Mul N] [Mul P] [SMul M N] [SMul M P] [IsScalarTower M N N]
    [IsScalarTower M P P] : IsScalarTower M (N × P) (N × P) where
  smul_assoc c x y := by simp [smul_def, mul_def, smul_mul_assoc]

@[to_additive]
/--
Instance `mulAction` / 实例 `mulAction`

English:
instance mulAction
  signature: [Monoid M] [MulAction M α] [MulAction M β]
  body: by ext <;> exact mul_smul ..
  one_smul _ := by ext <;> exact one_smul ..

中文:
实例 mulAction
  签名: [Monoid M] [MulAction M α] [MulAction M β]
  定义体: by ext <;> exact mul_smul ..
  one_smul _ := by ext <;> exact one_smul ..

Depends on / 依赖: mul_smul, one_smul
-/
instance mulAction [Monoid M] [MulAction M α] [MulAction M β] : MulAction M (α × β) where
  mul_smul _ _ _ := by ext <;> exact mul_smul ..
  one_smul _ := by ext <;> exact one_smul ..

end Prod

/-! ### Scalar multiplication as a homomorphism -/

section BundledSMul

/-- Scalar multiplication as a multiplicative homomorphism. -/
@[simps]
/--
Definition of `smulMulHom` / `smulMulHom` 的定义

English:
definition smulMulHom
  signature: [Monoid α] [Mul β] [MulAction α β] [IsScalarTower α β β] [SMulCommClass α β β]
  body: a.1 • a.2
  map_mul' _ _ := (smul_mul_smul_comm _ _ _ _).symm

中文:
定义 smulMulHom
  签名: [Monoid α] [Mul β] [MulAction α β] [IsScalarTower α β β] [SMulCommClass α β β]
  定义体: a.1 • a.2
  map_mul' _ _ := (smul_mul_smul_comm _ _ _ _).symm
-/
def smulMulHom [Monoid α] [Mul β] [MulAction α β] [IsScalarTower α β β] [SMulCommClass α β β] :
    α × β ->ₙ* β where
  toFun a := a.1 • a.2
  map_mul' _ _ := (smul_mul_smul_comm _ _ _ _).symm

/-- Scalar multiplication as a monoid homomorphism. -/
@[simps]
/--
Definition of `smulMonoidHom` / `smulMonoidHom` 的定义

English:
definition smulMonoidHom
  signature: [Monoid α] [MulOneClass β] [MulAction α β] [IsScalarTower α β β]
  body: { smulMulHom with map_one' := one_smul _ _ }

中文:
定义 smulMonoidHom
  签名: [Monoid α] [MulOneClass β] [MulAction α β] [IsScalarTower α β β]
  定义体: { smulMulHom with map_one' := one_smul _ _ }

Depends on / 依赖: map_one, one_smul, smulMulHom
-/
def smulMonoidHom [Monoid α] [MulOneClass β] [MulAction α β] [IsScalarTower α β β]
    [SMulCommClass α β β] : α × β ->* β :=
  { smulMulHom with map_one' := one_smul _ _ }

end BundledSMul

section Action_by_Prod
variable (M N α) [Monoid M] [Monoid N]

/-- Construct a `MulAction` by a product monoid from `MulAction`s by the factors.
  This is not an instance to avoid diamonds for example when `α := M × N`. -/
@[to_additive AddAction.prodOfVAddCommClass
/-- Construct an `AddAction` by a product monoid from `AddAction`s by the factors.
This is not an instance to avoid diamonds for example when `α := M × N`. -/]
/--
Definition of `MulAction.prodOfSMulCommClass` / `MulAction.prodOfSMulCommClass` 的定义

English:
abbreviation MulAction.prodOfSMulCommClass
  signature: [MulAction M α] [MulAction N α] [SMulCommClass M N α]
  body: mn.1 • mn.2 • a
  one_smul a := (one_smul M _).trans (one_smul N a)
  mul_smul x y a := by
    change (x.1 * y.1) • (x.2 * y.2) • a = x.1 • x.2 • y.1 • y.2 • a
    rw [mul_smul]; rw [mul_smul]; rw [smul_comm y.1 x.2]

中文:
缩写 MulAction.prodOfSMulCommClass
  签名: [MulAction M α] [MulAction N α] [SMulCommClass M N α]
  定义体: mn.1 • mn.2 • a
  one_smul a := (one_smul M _).trans (one_smul N a)
  mul_smul x y a := by
    change (x.1 * y.1) • (x.2 * y.2) • a = x.1 • x.2 • y.1 • y.2 • a
    rw [mul_smul]; rw [mul_smul]; rw [smul_comm y.1 x.2]
-/
abbrev MulAction.prodOfSMulCommClass [MulAction M α] [MulAction N α] [SMulCommClass M N α] :
    MulAction (M × N) α where
  smul mn a := mn.1 • mn.2 • a
  one_smul a := (one_smul M _).trans (one_smul N a)
  mul_smul x y a := by
    change (x.1 * y.1) • (x.2 * y.2) • a = x.1 • x.2 • y.1 • y.2 • a
    rw [mul_smul]; rw [mul_smul]; rw [smul_comm y.1 x.2]

/-- A `MulAction` by a product monoid is equivalent to commuting `MulAction`s by the factors. -/
@[to_additive AddAction.prodEquiv
/-- An `AddAction` by a product monoid is equivalent to commuting `AddAction`s by the factors. -/]
/--
Definition of `MulAction.prodEquiv` / `MulAction.prodEquiv` 的定义

English:
definition MulAction.prodEquiv
  signature: :
  body: letI instM := MulAction.compHom α (.inl M N)
    letI instN := MulAction.compHom α (.inr M N)
    ⟨instM, instN,
    { smul_comm := fun m n a => by
        change (m, (1 : N)) • ((1 : M), n) • a = ((1 : M), n) • (m, (1 : N)) • a
        simp_rw [smul_smul, Prod.mk_mul_mk, mul_one, one_mul] }⟩
  invF

中文:
定义 MulAction.prodEquiv
  签名: :
  定义体: letI instM := MulAction.compHom α (.inl M N)
    letI instN := MulAction.compHom α (.inr M N)
    ⟨instM, instN,
    { smul_comm := fun m n a => by
        change (m, (1 : N)) • ((1 : M), n) • a = ((1 : M), n) • (m, (1 : N)) • a
        simp_rw [smul_smul, Prod.mk_mul_mk, mul_one, one_mul] }⟩
  invF

Depends on / 依赖: MulAction, MulAction.compHom, MulAction.prodOfSMulCommClass, Prod.mk_, Prod.mk_mul_mk, _insts, compHom, invFun, left_inv, mk_mul_mk, mul_one, mul_smul, one_mul, prodOfSMulCommClass, simp_rw, smul_comm, smul_smul
-/
def MulAction.prodEquiv :
    MulAction (M × N) α ≃ Σ' (_ : MulAction M α) (_ : MulAction N α), SMulCommClass M N α where
  toFun _ :=
    letI instM := MulAction.compHom α (.inl M N)
    letI instN := MulAction.compHom α (.inr M N)
    ⟨instM, instN,
    { smul_comm := fun m n a => by
        change (m, (1 : N)) • ((1 : M), n) • a = ((1 : M), n) • (m, (1 : N)) • a
        simp_rw [smul_smul, Prod.mk_mul_mk, mul_one, one_mul] }⟩
  invFun _insts :=
    letI := _insts.1; letI := _insts.2.1; have := _insts.2.2
    MulAction.prodOfSMulCommClass M N α
  left_inv := by
    rintro ⟨_⟩; dsimp only; ext ⟨m, n⟩ a
    change (m, (1 : N)) • ((1 : M), n) • a = _
    rw [← mul_smul]; rw [Prod.mk_mul_mk]; rw [mul_one]; rw [one_mul]; rfl
  right_inv := by
    rintro ⟨hM, hN, -⟩
    dsimp only; congr 1
    · ext m a; (conv_rhs => rw [← hN.one_smul a]); rfl
    congr 1
    · funext; congr; ext m a; (conv_rhs => rw [← hN.one_smul a]); rfl
    · ext n a; (conv_rhs => rw [← hM.one_smul (SMul.smul n a)]); rfl
    · exact proof_irrel_heq ..

end Action_by_Prod
