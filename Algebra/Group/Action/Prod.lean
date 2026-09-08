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
/-
**Prod.isScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：isScalarTower [SMul M N] [IsScalarTower M N α] [IsScalarTower M N β] : IsS
calarTower M N (α × β) where smul_assoc _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance isScalarTower [SMul M N] [IsScalarTower M N α] [IsScalarTower M N β] :
    IsScalarTower M N (α × β) where
  smul_assoc _ _ _ := by ext <;> exact smul_assoc ..

@[to_additive]
/-
**Prod.smulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：smulCommClass [SMulCommClass M N α] [SMulCommClass M N β] : SMulCommClass 
M N (α × β) where smul_comm _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance smulCommClass [SMulCommClass M N α] [SMulCommClass M N β] : SMulCommClass M N (α × β) where
  smul_comm _ _ _ := by ext <;> exact smul_comm ..

@[to_additive]
/-
**Prod.isCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：isCentralScalar [SMul Mᵐᵒᵖ α] [SMul Mᵐᵒᵖ β] [IsCentralScalar M α] [IsCentr
alScalar M β] : IsCentralScalar M (α × β) where op_smul_eq_smul _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
-/
instance isCentralScalar [SMul Mᵐᵒᵖ α] [SMul Mᵐᵒᵖ β] [IsCentralScalar M α] [IsCentralScalar M β] :
    IsCentralScalar M (α × β) where
  op_smul_eq_smul _ _ := Prod.ext (op_smul_eq_smul _ _) (op_smul_eq_smul _ _)

@[to_additive]
/-
**Prod.faithfulSMulLeft** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：faithfulSMulLeft [FaithfulSMul M α] [Nonempty β] : FaithfulSMul M (α × β) 
where eq_of_smul_eq_smul h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
instance faithfulSMulLeft [FaithfulSMul M α] [Nonempty β] : FaithfulSMul M (α × β) where
  eq_of_smul_eq_smul h :=
    let ⟨b⟩ := ‹Nonempty β›
    eq_of_smul_eq_smul fun a : α => by injection h (a, b)

@[to_additive]
/-
**Prod.faithfulSMulRight** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：faithfulSMulRight [Nonempty α] [FaithfulSMul M β] : FaithfulSMul M (α × β)
 where eq_of_smul_eq_smul h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
instance faithfulSMulRight [Nonempty α] [FaithfulSMul M β] : FaithfulSMul M (α × β) where
  eq_of_smul_eq_smul h :=
    let ⟨a⟩ := ‹Nonempty α›
    eq_of_smul_eq_smul fun b : β => by injection h (a, b)

end

@[to_additive]
/-
**Prod.smulCommClassBoth** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：smulCommClassBoth [Mul N] [Mul P] [SMul M N] [SMul M P] [SMulCommClass M N
 N] [SMulCommClass M P P] : SMulCommClass M (N × P) (N × P) where smul_comm c x 
y
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance smulCommClassBoth [Mul N] [Mul P] [SMul M N] [SMul M P] [SMulCommClass M N N]
    [SMulCommClass M P P] : SMulCommClass M (N × P) (N × P) where
  smul_comm c x y := by simp [smul_def, mul_def, mul_smul_comm]
/-
**Prod.isScalarTowerBoth** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：isScalarTowerBoth [Mul N] [Mul P] [SMul M N] [SMul M P] [IsScalarTower M N
 N] [IsScalarTower M P P] : IsScalarTower M (N × P) (N × P) where smul_assoc c x
 y
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance isScalarTowerBoth [Mul N] [Mul P] [SMul M N] [SMul M P] [IsScalarTower M N N]
    [IsScalarTower M P P] : IsScalarTower M (N × P) (N × P) where
  smul_assoc c x y := by simp [smul_def, mul_def, smul_mul_assoc]

@[to_additive]
/-
**Prod.mulAction** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：mulAction [Monoid M] [MulAction M α] [MulAction M β] : MulAction M (α × β)
 where mul_smul _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulAction [Monoid M] [MulAction M α] [MulAction M β] : MulAction M (α × β) where
  mul_smul _ _ _ := by ext <;> exact mul_smul ..
  one_smul _ := by ext <;> exact one_smul ..

end Prod

/-! ### Scalar multiplication as a homomorphism -/

section BundledSMul

/-- Scalar multiplication as a multiplicative homomorphism. -/
@[simps]
/-
**smulMulHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：smulMulHom [Monoid α] [Mul β] [MulAction α β] [IsScalarTower α β β] [SMulC
ommClass α β β] : α × β ->ₙ* β where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Scalar multiplication as a multiplicative homomorphism.
-/
def smulMulHom [Monoid α] [Mul β] [MulAction α β] [IsScalarTower α β β] [SMulCommClass α β β] :
    α × β →ₙ* β where
  toFun a := a.1 • a.2
  map_mul' _ _ := (smul_mul_smul_comm _ _ _ _).symm

/-- Scalar multiplication as a monoid homomorphism. -/
@[simps]
/-
**smulMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：smulMonoidHom [Monoid α] [MulOneClass β] [MulAction α β] [IsScalarTower α 
β β] [SMulCommClass α β β] : α × β ->* β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Scalar multiplication as a monoid homomorphism.
-/
def smulMonoidHom [Monoid α] [MulOneClass β] [MulAction α β] [IsScalarTower α β β]
    [SMulCommClass α β β] : α × β →* β :=
  { smulMulHom with map_one' := one_smul _ _ }

end BundledSMul

section Action_by_Prod
variable (M N α) [Monoid M] [Monoid N]

/-- Construct a `MulAction` by a product monoid from `MulAction`s by the factors.
  This is not an instance to avoid diamonds for example when `α := M × N`. -/
@[to_additive AddAction.prodOfVAddCommClass
/-- Construct an `AddAction` by a product monoid from `AddAction`s by the factors.
This is not an instance to avoid diamonds for example when `α := M × N`. -/]
/-
**MulAction.prodOfSMulCommClass** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：MulAction.prodOfSMulCommClass [MulAction M α] [MulAction N α] [SMulCommCla
ss M N α] : MulAction (M × N) α where smul mn a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev MulAction.prodOfSMulCommClass [MulAction M α] [MulAction N α] [SMulCommClass M N α] :
    MulAction (M × N) α where
  smul mn a := mn.1 • mn.2 • a
  one_smul a := (one_smul M _).trans (one_smul N a)
  mul_smul x y a := by
    change (x.1 * y.1) • (x.2 * y.2) • a = x.1 • x.2 • y.1 • y.2 • a
    rw [mul_smul, mul_smul, smul_comm y.1 x.2]

/-- A `MulAction` by a product monoid is equivalent to commuting `MulAction`s by the factors. -/
@[to_additive AddAction.prodEquiv
/-- An `AddAction` by a product monoid is equivalent to commuting `AddAction`s by the factors. -/]
/-
**MulAction.prodEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulAction.prodEquiv : MulAction (M × N) α ≃ Σ' (_ : MulAction M α) (_ : Mu
lAction N α), SMulCommClass M N α where toFun _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MulAction.prodEquiv :
    MulAction (M × N) α ≃ Σ' (_ : MulAction M α) (_ : MulAction N α), SMulCommClass M N α where
  toFun _ :=
    letI instM := MulAction.compHom α (.inl M N)
    letI instN := MulAction.compHom α (.inr M N)
    ⟨instM, instN,
    { smul_comm := fun m n a ↦ by
        change (m, (1 : N)) • ((1 : M), n) • a = ((1 : M), n) • (m, (1 : N)) • a
        simp_rw [smul_smul, Prod.mk_mul_mk, mul_one, one_mul] }⟩
  invFun _insts :=
    letI := _insts.1; letI := _insts.2.1; have := _insts.2.2
    MulAction.prodOfSMulCommClass M N α
  left_inv := by
    rintro ⟨_⟩; dsimp only; ext ⟨m, n⟩ a
    change (m, (1 : N)) • ((1 : M), n) • a = _
    rw [← mul_smul, Prod.mk_mul_mk, mul_one, one_mul]; rfl
  right_inv := by
    rintro ⟨hM, hN, -⟩
    dsimp only; congr 1
    · ext m a; (conv_rhs => rw [← hN.one_smul a]); rfl
    congr 1
    · funext; congr; ext m a; (conv_rhs => rw [← hN.one_smul a]); rfl
    · ext n a; (conv_rhs => rw [← hM.one_smul (SMul.smul n a)]); rfl
    · exact proof_irrel_heq ..

end Action_by_Prod

