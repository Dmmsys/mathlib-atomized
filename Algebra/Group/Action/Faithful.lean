/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Action.Defs

/-!
# Faithful group actions

This file provides typeclasses for faithful actions.

## Notation

- `a • b` is used as notation for `SMul.smul a b`.
- `a +ᵥ b` is used as notation for `VAdd.vadd a b`.

## Implementation details

This file should avoid depending on other parts of `GroupTheory`, to avoid import cycles.
More sophisticated lemmas belong in `GroupTheory.GroupAction`.

## Tags

group action
-/

public section

assert_not_exists MonoidWithZero

open Function (Injective Surjective)

variable {M G α : Type*}

/-! ### Faithful actions -/

/-- Typeclass for faithful actions. -/
/-
**FaithfulVAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_4) → (P : Type u_5) → [VAdd G P] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for faithful actions.
-/
class FaithfulVAdd (G : Type*) (P : Type*) [VAdd G P] : Prop where
  /-- Two elements `g₁` and `g₂` are equal whenever they act in the same way on all points. -/
  eq_of_vadd_eq_vadd : ∀ {g₁ g₂ : G}, (∀ p : P, g₁ +ᵥ p = g₂ +ᵥ p) → g₁ = g₂

/-- Typeclass for faithful actions. -/
@[to_additive]
/-
**FaithfulSMul** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_4) → (α : Type u_5) → [SMul M α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for faithful actions.
-/
class FaithfulSMul (M : Type*) (α : Type*) [SMul M α] : Prop where
  /-- Two elements `m₁` and `m₂` are equal whenever they act in the same way on all points. -/
  eq_of_smul_eq_smul : ∀ {m₁ m₂ : M}, (∀ a : α, m₁ • a = m₂ • a) → m₁ = m₂

export FaithfulSMul (eq_of_smul_eq_smul)
export FaithfulVAdd (eq_of_vadd_eq_vadd)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance (priority := low) [SMul M α] [Subsingleton M] : FaithfulSMul M α :=
  ⟨fun _ ↦ Subsingleton.elim ..⟩

@[to_additive]
/-
**smul_left_injective'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_left_injective' [SMul M α] [FaithfulSMul M α] : Injective ((· • ·) : 
M -> α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
lemma smul_left_injective' [SMul M α] [FaithfulSMul M α] : Injective ((· • ·) : M → α → α) :=
  fun _ _ h ↦ FaithfulSMul.eq_of_smul_eq_smul (congr_fun h)

/-- `instSMulOfMul` is faithful when there is a (right) identity. -/
@[to_additive /-- `instVAddOfAdd` is faithful when there is a (right) identity. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`instSMulOfMul` is faithful when there is a (right) identity.
-/
instance (R : Type*) [MulOneClass R] : FaithfulSMul R R where
  eq_of_smul_eq_smul {r₁ r₂} h := by simpa using h 1

/-- `Mul.toSMulMulOpposite` is faithful when there is a (left) identity. -/
@[to_additive /-- `Add.toVAddAddOpposite` is faithful when there is a (left) identity. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Mul.toSMulMulOpposite` is faithful when there is a (left) identity.
-/
instance (R : Type*) [MulOneClass R] : FaithfulSMul Rᵐᵒᵖ R where
  eq_of_smul_eq_smul {r₁ r₂} h := by simpa using h 1

/-- `instSMulOfMul` is faithful when multiplication is right cancellative. -/
@[to_additive /-- `instVAddOfAdd` is faithful when addition is right cancellative. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`instSMulOfMul` is faithful when multiplication is right cancellative.
-/
instance (R : Type*) [Mul R] [IsRightCancelMul R] : FaithfulSMul R R where
  eq_of_smul_eq_smul {r₁ r₂} h := by simpa using h r₁

/-- `Mul.toSMulMulOpposite` is faithful when multiplication is left cancellative -/
@[to_additive /-- `Add.toVAddAddOpposite` is faithful when addition is left cancellative -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Mul.toSMulMulOpposite` is faithful when multiplication is left cancellative
-/
instance (R : Type*) [Mul R] [IsLeftCancelMul R] : FaithfulSMul Rᵐᵒᵖ R where
  eq_of_smul_eq_smul {r₁ r₂} h := by simpa using h r₁.unop

/-- `Monoid.toMulAction` is faithful on cancellative monoids. -/
@[to_additive (attr :=
  deprecated "subsumed by `instFaithfulSMul` or `instFaithfulSMulOfIsRightCancelMul`"
  (since := "2026-02-03"))
  /-- `AddMonoid.toAddAction` is faithful on additive cancellative monoids. -/]
/-
**RightCancelMonoid.faithfulSMul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RightCancelMonoid.faithfulSMul [RightCancelMonoid α] : FaithfulSMul α α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instFaithfulSMulOfIsRightCancelMul`：∀ (R : Type u_4) [inst : Mul R] [IsR
ightCancelMul R], FaithfulSMul R R
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
-/
lemma RightCancelMonoid.faithfulSMul [RightCancelMonoid α] : FaithfulSMul α α :=
  inferInstance

/-- `Monoid.toOppositeMulAction` is faithful on cancellative monoids. -/
@[to_additive (attr :=
    deprecated "subsumed by `instFaithfulSMulMulOpposite` or \
    `instFaithfulSMulMulOppositeOfIsLeftCancelMul`"
    (since := "2026-02-03"))
  /-- `AddMonoid.toOppositeAddAction` is faithful on additive cancellative monoids. -/]
/-
**LeftCancelMonoid.to_faithfulSMul_mulOpposite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LeftCancelMonoid.to_faithfulSMul_mulOpposite [LeftCancelMonoid α] : Faithf
ulSMul αᵐᵒᵖ α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instFaithfulSMulMulOppositeOfIsLeftCancelMul`：∀ (R : Type u_4) [inst : M
ul R] [IsLeftCancelMul R], FaithfulSMul Rᵐᵒᵖ R
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
-/
lemma LeftCancelMonoid.to_faithfulSMul_mulOpposite [LeftCancelMonoid α] : FaithfulSMul αᵐᵒᵖ α :=
  inferInstance

@[to_additive]
/-
**faithfulSMul_iff_injective_smul_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：faithfulSMul_iff_injective_smul_one (R A : Type*) [MulOneClass A] [SMul R 
A] [IsScalarTower R A A] : FaithfulSMul R A ↔ Injective (fun r : R => r • (1 : A
))
参数：R A : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
-/
lemma faithfulSMul_iff_injective_smul_one (R A : Type*)
    [MulOneClass A] [SMul R A] [IsScalarTower R A A] :
    FaithfulSMul R A ↔ Injective (fun r : R ↦ r • (1 : A)) := by
  refine ⟨fun ⟨h⟩ {r₁ r₂} hr ↦ h fun a ↦ ?_, fun h ↦ ⟨fun {r₁ r₂} hr ↦ h ?_⟩⟩
  · simp only at hr
    rw [← one_mul a, ← smul_mul_assoc, ← smul_mul_assoc, hr]
  · simpa using hr 1

@[to_additive]
/-
**faithfulSMul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：faithfulSMul_iff [Group G] [MulAction G α] : FaithfulSMul G α ↔ (forall g 
: G, (forall a : α, g • a = a) -> g = 1)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_inv_of_mul_eq_one_left`：eq_inv_of_mul_eq_one_left (h : a * b = 1) : a
 = b⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
-/
theorem faithfulSMul_iff [Group G] [MulAction G α] :
    FaithfulSMul G α ↔ (∀ g : G, (∀ a : α, g • a = a) → g = 1) := by
  refine ⟨fun h a ha ↦ h.eq_of_smul_eq_smul ?_, fun h ↦ ⟨fun {a₁ a₂} h' ↦ ?_⟩⟩
  · simpa only [one_smul]
  · rw [← inv_inv a₂, eq_inv_of_mul_eq_one_left (h (a₂⁻¹ * a₁) ?_), inv_inv]
    simpa only [mul_smul, inv_smul_eq_iff] using h'

@[to_additive]
/-
**FaithfulSMul.tower_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：FaithfulSMul.tower_bot (R S T : Type*) [Monoid S] [MulOneClass T] [SMul R 
S] [SMul R T] [MulAction S T] [IsScalarTower R S S] [IsScalarTower R T T] [IsSca
larTower R S T] [FaithfulSMul R T] : FaithfulSMul R S
参数：R S T : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `faithfulSMul_iff_injective_smul_one`：faithfulSMul_iff_injective_smul_one
 (R A : Type*) [MulOneClass A] [SMul R A] [IsScalarTower R A A] : FaithfulSMul R
 A ↔ Injective (fun r : R…
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma FaithfulSMul.tower_bot (R S T : Type*) [Monoid S] [MulOneClass T]
    [SMul R S] [SMul R T] [MulAction S T]
    [IsScalarTower R S S] [IsScalarTower R T T]
    [IsScalarTower R S T] [FaithfulSMul R T] : FaithfulSMul R S := by
  rw [faithfulSMul_iff_injective_smul_one]
  refine .of_comp (f := (· • (1 : T))) ?_
  simpa [Function.comp_def, one_smul, ← faithfulSMul_iff_injective_smul_one]

@[to_additive]
/-
**FaithfulSMul.trans** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：FaithfulSMul.trans (R S T : Type*) [Monoid S] [MulOneClass T] [SMul R S] [
IsScalarTower R S S] [MulAction S T] [IsScalarTower S T T] [SMul R T] [IsScalarT
ower R T T] [IsScalarTower R S T] [FaithfulSMul R S] [FaithfulSMul S T] : Faithf
ulSMul R T
参数：R S T : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `faithfulSMul_iff_injective_smul_one`：faithfulSMul_iff_injective_smul_one
 (R A : Type*) [MulOneClass A] [SMul R A] [IsScalarTower R A A] : FaithfulSMul R
 A ↔ Injective (fun r : R…
-/
lemma FaithfulSMul.trans (R S T : Type*) [Monoid S] [MulOneClass T]
    [SMul R S] [IsScalarTower R S S] [MulAction S T] [IsScalarTower S T T]
    [SMul R T] [IsScalarTower R T T] [IsScalarTower R S T] [FaithfulSMul R S]
    [FaithfulSMul S T] : FaithfulSMul R T := by
  simpa [faithfulSMul_iff_injective_smul_one, Function.comp_def] using
    ((faithfulSMul_iff_injective_smul_one S T).mp ‹_›).comp
      ((faithfulSMul_iff_injective_smul_one R S).mp ‹_›)

/--
Let `Q / P / N / M` be a tower. If `Q / N / M`, `Q / P / M` and `Q / P / N` are
scalar towers, then `P / N / M` is also a scalar tower.
-/
/-
**IsScalarTower.to** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `Q / P / N / M` be a tower. If `Q / N / M`, `Q / P / M` and `Q / P / N` are
scalar towers, then `P / N / M` is also a scalar tower.
-/
@[to_additive] lemma IsScalarTower.to₁₂₃ (M N P Q)
    [SMul M N] [SMul M P] [SMul M Q] [SMul N P] [SMul N Q] [SMul P Q] [FaithfulSMul P Q]
    [IsScalarTower M N Q] [IsScalarTower M P Q] [IsScalarTower N P Q] : IsScalarTower M N P where
  smul_assoc m n p := by simp_rw [← (smul_left_injective' (α := Q)).eq_iff, smul_assoc]

open MulOpposite in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul α M] [FaithfulSMul α M] : FaithfulSMul α Mᵐᵒᵖ where
  eq_of_smul_eq_smul h := FaithfulSMul.eq_of_smul_eq_smul fun m ↦ op_inj.mp <| h (op m)
