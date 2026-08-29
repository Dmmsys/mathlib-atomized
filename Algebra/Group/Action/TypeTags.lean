/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Additive and Multiplicative for group actions

## Tags

group action
-/

public section

assert_not_exists MonoidWithZero MonoidHom

open Function (Injective Surjective)

variable {M α β γ : Type*}

section

open Additive Multiplicative

/--
Instance `Additive.vadd` / 实例 `Additive.vadd`

English:
instance Additive.vadd
  signature: [SMul α β]
  body: (a.toMul • ·)

中文:
实例 Additive.vadd
  签名: [SMul α β]
  定义体: (a.toMul • ·)

Depends on / 依赖: a.toMul
-/
instance Additive.vadd [SMul α β] : VAdd (Additive α) β where vadd a := (a.toMul • ·)

/--
Instance `Multiplicative.smul` / 实例 `Multiplicative.smul`

English:
instance Multiplicative.smul
  signature: [VAdd α β]
  body: (a.toAdd +ᵥ ·)

中文:
实例 Multiplicative.smul
  签名: [VAdd α β]
  定义体: (a.toAdd +ᵥ ·)

Depends on / 依赖: a.toAdd
-/
instance Multiplicative.smul [VAdd α β] : SMul (Multiplicative α) β where smul a := (a.toAdd +ᵥ ·)

/--
lemma `toMul_smul` / 引理 `toMul_smul`

English:
lemma toMul_smul
  given: [SMul α β] (a : Additive α) (b : β)
  statement: (a.toMul : α) • b = a +ᵥ b
  proof: rfl

中文:
引理 toMul_smul
  条件: [SMul α β] (a : Additive α) (b : β)
  结论: (a.toMul : α) • b = a +ᵥ b
  证明: rfl
-/
@[simp] lemma toMul_smul [SMul α β] (a : Additive α) (b : β) : (a.toMul : α) • b = a +ᵥ b := rfl

/--
lemma `ofMul_vadd` / 引理 `ofMul_vadd`

English:
lemma ofMul_vadd
  given: [SMul α β] (a : α) (b : β)
  statement: ofMul a +ᵥ b = a • b
  proof: rfl

中文:
引理 ofMul_vadd
  条件: [SMul α β] (a : α) (b : β)
  结论: ofMul a +ᵥ b = a • b
  证明: rfl
-/
@[simp] lemma ofMul_vadd [SMul α β] (a : α) (b : β) : ofMul a +ᵥ b = a • b := rfl

/--
lemma `toAdd_vadd` / 引理 `toAdd_vadd`

English:
lemma toAdd_vadd
  given: [VAdd α β] (a : Multiplicative α) (b : β)
  statement: (a.toAdd : α) +ᵥ b = a • b
  proof: rfl

中文:
引理 toAdd_vadd
  条件: [VAdd α β] (a : Multiplicative α) (b : β)
  结论: (a.toAdd : α) +ᵥ b = a • b
  证明: rfl
-/
@[simp] lemma toAdd_vadd [VAdd α β] (a : Multiplicative α) (b : β) : (a.toAdd : α) +ᵥ b = a • b :=
  rfl

/--
lemma `ofAdd_smul` / 引理 `ofAdd_smul`

English:
lemma ofAdd_smul
  given: [VAdd α β] (a : α) (b : β)
  statement: ofAdd a • b = a +ᵥ b
  proof: rfl

中文:
引理 ofAdd_smul
  条件: [VAdd α β] (a : α) (b : β)
  结论: ofAdd a • b = a +ᵥ b
  证明: rfl
-/
@[simp] lemma ofAdd_smul [VAdd α β] (a : α) (b : β) : ofAdd a • b = a +ᵥ b := rfl

/--
Instance `Additive.addAction` / 实例 `Additive.addAction`

English:
instance Additive.addAction
  signature: [Monoid α] [MulAction α β]
  body: MulAction.one_smul
  add_vadd := mul_smul (α := α)

中文:
实例 Additive.addAction
  签名: [Monoid α] [MulAction α β]
  定义体: MulAction.one_smul
  add_vadd := mul_smul (α := α)

Depends on / 依赖: MulAction, MulAction.one_smul, one_smul
-/
instance Additive.addAction [Monoid α] [MulAction α β] : AddAction (Additive α) β where
  zero_vadd := MulAction.one_smul
  add_vadd := mul_smul (α := α)

/--
Instance `Multiplicative.mulAction` / 实例 `Multiplicative.mulAction`

English:
instance Multiplicative.mulAction
  signature: [AddMonoid α] [AddAction α β]
  body: AddAction.zero_vadd
  mul_smul := add_vadd (G := α)

中文:
实例 Multiplicative.mulAction
  签名: [AddMonoid α] [AddAction α β]
  定义体: AddAction.zero_vadd
  mul_smul := add_vadd (G := α)

Depends on / 依赖: AddAction, AddAction.zero_vadd, zero_vadd
-/
instance Multiplicative.mulAction [AddMonoid α] [AddAction α β] :
    MulAction (Multiplicative α) β where
  one_smul := AddAction.zero_vadd
  mul_smul := add_vadd (G := α)

/--
Instance `Additive.vaddCommClass` / 实例 `Additive.vaddCommClass`

English:
instance Additive.vaddCommClass
  signature: [SMul α γ] [SMul β γ] [SMulCommClass α β γ]
  body: ⟨@smul_comm α β _ _ _ _⟩

中文:
实例 Additive.vaddCommClass
  签名: [SMul α γ] [SMul β γ] [SMulCommClass α β γ]
  定义体: ⟨@smul_comm α β _ _ _ _⟩

Depends on / 依赖: smul_comm
-/
instance Additive.vaddCommClass [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    VAddCommClass (Additive α) (Additive β) γ :=
  ⟨@smul_comm α β _ _ _ _⟩

/--
Instance `Multiplicative.smulCommClass` / 实例 `Multiplicative.smulCommClass`

English:
instance Multiplicative.smulCommClass
  signature: [VAdd α γ] [VAdd β γ] [VAddCommClass α β γ]
  body: ⟨@vadd_comm α β _ _ _ _⟩

中文:
实例 Multiplicative.smulCommClass
  签名: [VAdd α γ] [VAdd β γ] [VAddCommClass α β γ]
  定义体: ⟨@vadd_comm α β _ _ _ _⟩

Depends on / 依赖: vadd_comm
-/
instance Multiplicative.smulCommClass [VAdd α γ] [VAdd β γ] [VAddCommClass α β γ] :
    SMulCommClass (Multiplicative α) (Multiplicative β) γ :=
  ⟨@vadd_comm α β _ _ _ _⟩

end
