/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Group.Action.Faithful
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Data.Fintype.Basic

/-!
# Transfer algebraic structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

public section

assert_not_exists MonoidWithZero

namespace Equiv
variable {M N O α β : Type*}

variable (M) [Monoid M] in
/-- Transfer `MulAction` across an `Equiv` -/
@[to_additive /-- Transfer `AddAction` across an `Equiv` -/]
/-
**Equiv.mulAction** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：(M : Type u_1) → {α : Type u_4} → {β : Type u_5} → [inst : Monoid M] → α ≃
 β → [MulAction M β] → MulAction M α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer `MulAction` across an `Equiv`
-/
protected abbrev mulAction (e : α ≃ β) [MulAction M β] : MulAction M α where
  __ := e.smul M
  one_smul := by simp [smul_def]
  mul_smul := by simp [smul_def, mul_smul]

variable (M N) [SMul M β] [SMul N β] in
/-- Transfer `SMulCommClass` across an `Equiv` -/
@[to_additive /-- Transfer `VAddCommClass` across an `Equiv` -/]
/-
**Equiv.smulCommClass** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ (M : Type u_1) (N : Type u_2) {α : Type u_4} {β : Type u_5} [inst : SMul
 M β] [inst_1 : SMul N β] (e : α ≃ β)   [SMulCommClass M N β], SMulCommClass M N
 α
参数：M : Type u_1；N : Type u_2；e : α ≃ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Transfer `SMulCommClass` across an `Equiv`
-/
protected lemma smulCommClass (e : α ≃ β) [SMulCommClass M N β] :
    letI := e.smul M
    letI := e.smul N
    SMulCommClass M N α :=
  letI := e.smul M
  letI := e.smul N
  { smul_comm := by simp [smul_def, smul_comm] }

variable (M N) [SMul M N] [SMul M β] [SMul N β] in
/-- Transfer `IsScalarTower` across an `Equiv` -/
@[to_additive /-- Transfer `VAddAssocClass` across an `Equiv` -/]
/-
**Equiv.isScalarTower** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ (M : Type u_1) (N : Type u_2) {α : Type u_4} {β : Type u_5} [inst : SMul
 M N] [inst_1 : SMul M β] [inst_2 : SMul N β]   (e : α ≃ β) [IsScalarTower M N β
], IsScalarTower M N α
参数：M : Type u_1；N : Type u_2；e : α ≃ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Transfer `IsScalarTower` across an `Equiv`
-/
protected lemma isScalarTower (e : α ≃ β) [IsScalarTower M N β] :
    letI := e.smul M
    letI := e.smul N
    IsScalarTower M N α :=
  letI := e.smul M
  letI := e.smul N
  { smul_assoc := by simp [smul_def, smul_assoc] }

variable (M) [SMul M β] [SMul Mᵐᵒᵖ β] in
/-- Transfer `IsCentralScalar` across an `Equiv` -/
@[to_additive /-- Transfer `IsCentralVAdd` across an `Equiv` -/]
/-
**Equiv.isCentralScalar** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ (M : Type u_1) {α : Type u_4} {β : Type u_5} [inst : SMul M β] [inst_1 :
 SMul Mᵐᵒᵖ β] (e : α ≃ β)   [IsCentralScalar M β], IsCentralScalar M α
参数：M : Type u_1；e : α ≃ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Transfer `IsCentralScalar` across an `Equiv`
-/
protected lemma isCentralScalar (e : α ≃ β) [IsCentralScalar M β] :
    letI := e.smul M
    letI := e.smul Mᵐᵒᵖ
    IsCentralScalar M α :=
  letI := e.smul M
  letI := e.smul Mᵐᵒᵖ
  { op_smul_eq_smul := by simp [smul_def, op_smul_eq_smul] }

variable (M) [Monoid M] [Monoid O] in
/-- Transfer `MulDistribMulAction` across an `Equiv` -/
/-
**Equiv.mulDistribMulAction** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：(M : Type u_1) →   {N : Type u_2} →     {O : Type u_3} →       [inst : Mon
oid M] → [inst_1 : Monoid O] → (e : N ≃ O) → [MulDistribMulAction M O] → MulDist
ribMulAction M N
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer `MulDistribMulAction` across an `Equiv`
-/
protected abbrev mulDistribMulAction (e : N ≃ O) [MulDistribMulAction M O] :
    letI := e.monoid
    MulDistribMulAction M N :=
  letI := e.monoid
  { e.mulAction M with
    smul_one := by simp [one_def, smul_def, smul_one]
    smul_mul := by simp [mul_def, smul_def, smul_mul'] }

variable (M) [SMul M β] in
/-- Transfer `FaithfulSMul` across an `Equiv`.

See `FaithfulSMul.of_injective` for the general statement not about transferring. -/
@[to_additive /-- Transfer `FaithfulVAdd` across an `Equiv`

See `FaithfulVAdd.of_injective` for the general statement not about transferring. -/]
/-
**Equiv.faithfulSMul** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ (M : Type u_1) {α : Type u_4} {β : Type u_5} [inst : SMul M β] (e : α ≃ 
β) [FaithfulSMul M β], FaithfulSMul M α
参数：M : Type u_1；e : α ≃ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.forall_congr_right`：∀ {α : Sort u} {β : Sort v} {q : β → Prop} (e 
: α ≃ β), (∀ (a : α), q (e a)) ↔ ∀ (b : β), q b
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
-/
protected lemma faithfulSMul (e : α ≃ β) [FaithfulSMul M β] :
    letI := e.smul M
    FaithfulSMul M α :=
  letI := e.smul M
  { eq_of_smul_eq_smul {m₁ m₂} := by
      simpa [← e.forall_congr_right, smul_def] using eq_of_smul_eq_smul (α := β) }

end Equiv

