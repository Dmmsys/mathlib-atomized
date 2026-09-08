/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.GroupWithZero.InjSurj
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
public import Mathlib.Algebra.GroupWithZero.Pointwise.Finset

/-!
# Pointwise operations of finsets in a group with zero

This file proves properties of pointwise operations of finsets in a group with zero.
-/

@[expose] public section

assert_not_exists Ring

open scoped Pointwise

namespace Finset
variable {α β : Type*} [DecidableEq β]

/-- If scalar multiplication by elements of `α` sends `(0 : β)` to zero,
then the same is true for `(0 : Finset β)`. -/
@[instance_reducible]
/-
**Finset.smulZeroClass** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [DecidableEq β] → [inst : Zero β] → [SMu
lZeroClass α β] → SMulZeroClass α (Finset β)
参数：Finset β。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_zero`：∀ {α : Type u_2} [inst : Zero α], ↑0 = 0
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)

--- 原说明 ---
If scalar multiplication by elements of `α` sends `(0 : β)` to zero,
then the same is true for `(0 : Finset β)`.
-/
protected def smulZeroClass [Zero β] [SMulZeroClass α β] : SMulZeroClass α (Finset β) :=
  coe_injective.smulZeroClass ⟨_, coe_zero⟩ coe_smul_finset

/-- If the scalar multiplication `(· • ·) : α → β → β` is distributive,
then so is `(· • ·) : α → Finset β → Finset β`. -/
@[instance_reducible]
/-
**Finset.distribSMul** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} → [inst : DecidableEq β] → [inst_1 : Add
ZeroClass β] → [DistribSMul α β] → DistribSMul α (Finset β)
参数：Finset β。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)

--- 原说明 ---
If the scalar multiplication `(· • ·) : α → β → β` is distributive,
then so is `(· • ·) : α → Finset β → Finset β`.
-/
protected noncomputable def distribSMul [AddZeroClass β] [DistribSMul α β] :
    DistribSMul α (Finset β) :=
  coe_injective.distribSMul coeAddMonoidHom coe_smul_finset

/-- A distributive multiplicative action of a monoid on an additive monoid `β` gives a distributive
multiplicative action on `Finset β`. -/
@[instance_reducible]
/-
**Finset.distribMulAction** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : DecidableEq β] →       [in
st_1 : Monoid α] → [inst_2 : AddMonoid β] → [DistribMulAction α β] → DistribMulA
ction α (Finset β)
参数：Finset β。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)

--- 原说明 ---
A distributive multiplicative action of a monoid on an additive monoid `β` gives
 a distributive
multiplicative action on `Finset β`.
-/
protected noncomputable def distribMulAction [Monoid α] [AddMonoid β] [DistribMulAction α β] :
    DistribMulAction α (Finset β) :=
  coe_injective.distribMulAction coeAddMonoidHom coe_smul_finset

/-- A multiplicative action of a monoid on a monoid `β` gives a multiplicative action on `Set β`. -/
@[instance_reducible]
/-
**Finset.mulDistribMulAction** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : DecidableEq β] →       [in
st_1 : Monoid α] → [inst_2 : Monoid β] → [MulDistribMulAction α β] → MulDistribM
ulAction α (Finset β)
参数：Finset β。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)

--- 原说明 ---
A multiplicative action of a monoid on a monoid `β` gives a multiplicative actio
n on `Set β`.
-/
protected noncomputable def mulDistribMulAction [Monoid α] [Monoid β] [MulDistribMulAction α β] :
    MulDistribMulAction α (Finset β) :=
  coe_injective.mulDistribMulAction coeMonoidHom coe_smul_finset

scoped[Pointwise] attribute [instance] Finset.smulZeroClass Finset.distribSMul
  Finset.distribMulAction Finset.mulDistribMulAction
/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors (Finset α) :=
  Function.Injective.noZeroDivisors _ coe_injective coe_zero coe_mul

section SMulZeroClass
variable [Zero β] [SMulZeroClass α β] {s : Finset α} {t : Finset β} {a : α}

/-
**Finset.smul_zero_subset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：smul_zero_subset (s : Finset α) : s • (0 : Finset β) subseteq 0
参数：s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma smul_zero_subset (s : Finset α) : s • (0 : Finset β) ⊆ 0 := by simp [subset_iff, mem_smul]
/-
**Finset.Nonempty.smul_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq β] [inst_1 : Zero β] [
inst_2 : SMulZeroClass α β] {s : Finset α},   s.Nonempty → s • 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `Finset.smul_zero_subset`：smul_zero_subset (s : Finset α) : s • (0 : Fins
et β) subseteq 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma Nonempty.smul_zero (hs : s.Nonempty) : s • (0 : Finset β) = 0 :=
  s.smul_zero_subset.antisymm <| by simpa [mem_smul] using! hs
/-
**Finset.zero_mem_smul_finset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：zero_mem_smul_finset (h : (0 : β) in t) : (0 : β) in a • t
参数：h : (0 : β) in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.mem_smul_finset`：mem_smul_finset {x : β} : x in a • s ↔ exists y,
 y in s ∧ a • y = x
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
lemma zero_mem_smul_finset (h : (0 : β) ∈ t) : (0 : β) ∈ a • t :=
  mem_smul_finset.2 ⟨0, h, smul_zero _⟩

end SMulZeroClass

section SMulWithZero
variable [Zero α] [Zero β] [SMulWithZero α β] {s : Finset α} {t : Finset β}

/-!
Note that we have neither `SMulWithZero α (Finset β)` nor `SMulWithZero (Finset α) (Finset β)`
because `0 • ∅ ≠ 0`.
-/

/-
**Finset.zero_smul_subset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：zero_smul_subset (t : Finset β) : (0 : Finset α) • t subseteq 0
参数：t : Finset β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Note that we have neither `SMulWithZero α (Finset β)` nor `SMulWithZero (Finset 
α) (Finset β)`
because `0 • ∅ ≠ 0`.
-/
lemma zero_smul_subset (t : Finset β) : (0 : Finset α) • t ⊆ 0 := by simp [subset_iff, mem_smul]
/-
**Finset.Nonempty.zero_smul** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq β] [inst_1 : Zero α] [
inst_2 : Zero β] [inst_3 : SMulWithZero α β]   {t : Finset β}, t.Nonempty → 0 • 
t = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `Finset.zero_smul_subset`：zero_smul_subset (t : Finset β) : (0 : Finset α
) • t subseteq 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma Nonempty.zero_smul (ht : t.Nonempty) : (0 : Finset α) • t = 0 :=
  t.zero_smul_subset.antisymm <| by simpa [mem_smul] using! ht

/-- A nonempty set is scaled by zero to the singleton set containing zero. -/
/-
**Finset.zero_smul_finset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq β] [inst_1 : Zero α] [
inst_2 : Zero β] [inst_3 : SMulWithZero α β]   {s : Finset β}, s.Nonempty → 0 • 
s = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.coe_smul_finset`：coe_smul_finset (a : α) (s : Finset β) : ↑(a • s
) = a • (↑s : Set β)
· 使用定理 `Finset.coe_zero`：∀ {α : Type u_2} [inst : Zero α], ↑0 = 0
· 使用定理 `Set.zero_smul_set`：∀ {α : Type u_1} {β : Type u_2} [inst : Zero α] [inst
_1 : Zero β] [inst_2 : SMulWithZero α β] {s : Set β},   s.Nonempty → 0 • s = 0

--- 原说明 ---
A nonempty set is scaled by zero to the singleton set containing zero.
-/
@[simp] lemma zero_smul_finset {s : Finset β} (h : s.Nonempty) : (0 : α) • s = (0 : Finset β) :=
  coe_injective <| by simpa using @Set.zero_smul_set α _ _ _ _ _ h
/-
**Finset.zero_smul_finset_subset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：zero_smul_finset_subset (s : Finset β) : (0 : α) • s subseteq 0
参数：s : Finset β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.image_subset_iff`：image_subset_iff : s.image f subseteq t ↔ foral
l x in s, f x in t
· 使用定理 `Finset.mem_zero`：∀ {α : Type u_2} [inst : Zero α] {a : α}, a ∈ 0 ↔ a = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
lemma zero_smul_finset_subset (s : Finset β) : (0 : α) • s ⊆ 0 :=
  image_subset_iff.2 fun x _ ↦ mem_zero.2 <| zero_smul α x

end SMulWithZero

section GroupWithZero
variable [GroupWithZero α]

section MulAction
variable [MulAction α β] {s t : Finset β} {a : α} {b : β}

/-
**Finset.smul_mem_smul_finset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：smul_mem_smul_finset_iff (a : α) : a • b in a • s ↔ b in s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.mem_finset_image`：∀ {α : Type u_1} {β : Type u_2} [in
st : DecidableEq β] {f : α → β} {s : Finset α} {a : α},   Function.Injective f →
 (f a ∈ Finset.image f s …
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
-/
@[simp] lemma smul_mem_smul_finset_iff₀ (ha : a ≠ 0) : a • b ∈ a • s ↔ b ∈ s :=
  smul_mem_smul_finset_iff (Units.mk0 a ha)
/-
**Finset.inv_smul_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inv_smul_mem_iff : a⁻¹ • b in s ↔ b in a • s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.smul_mem_smul_finset_iff`：smul_mem_smul_finset_iff (a : α) : a • 
b in a • s ↔ b in s
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma inv_smul_mem_iff₀ (ha : a ≠ 0) : a⁻¹ • b ∈ s ↔ b ∈ a • s :=
  show _ ↔ _ ∈ Units.mk0 a ha • _ from inv_smul_mem_iff
/-
**Finset.mem_inv_smul_finset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_inv_smul_finset_iff : b in a⁻¹ • s ↔ a • b in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.smul_mem_smul_finset_iff`：smul_mem_smul_finset_iff (a : α) : a • 
b in a • s ↔ b in s
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_inv_smul_finset_iff₀ (ha : a ≠ 0) : b ∈ a⁻¹ • s ↔ a • b ∈ s :=
  show _ ∈ (Units.mk0 a ha)⁻¹ • _ ↔ _ from mem_inv_smul_finset_iff

@[simp]
/-
**Finset.smul_finset_subset_smul_finset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：smul_finset_subset_smul_finset_iff : a • s subseteq a • t ↔ s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_subset_image_iff`：image_subset_image_iff {t : Finset α} (hf
 : Injective f) : s.image f subseteq t.image f ↔ s subseteq t
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
-/
lemma smul_finset_subset_smul_finset_iff₀ (ha : a ≠ 0) : a • s ⊆ a • t ↔ s ⊆ t :=
  show Units.mk0 a ha • s ⊆ _ ↔ _ from smul_finset_subset_smul_finset_iff
/-
**Finset.pairwiseDisjoint_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pairwiseDisjoint_smul_iff {s : Set α} {t : Finset β} : s.PairwiseDisjoint 
(· • t) ↔ (s ×ˢ t : Set (α × β)).InjOn fun p => p.1 • p.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Finset.coe_smul_finset`：coe_smul_finset (a : α) (s : Finset β) : ↑(a • s
) = a • (↑s : Set β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pairwiseDisjoint_smul_iff₀ {s : Set α} {t : Finset β} (hs : ∀ a ∈ s, a ≠ 0) :
    s.PairwiseDisjoint (· • t) ↔ (s ×ˢ t : Set (α × β)).InjOn fun p => p.1 • p.2 := by
  simp_rw [← pairwiseDisjoint_coe, coe_smul_finset]
  exact Set.pairwiseDisjoint_image_right_iff (fun a ha => MulAction.injective₀ (hs a ha))
/-
**Finset.smul_finset_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：smul_finset_subset_iff : a • s subseteq t ↔ s subseteq a⁻¹ • t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.coe_smul_finset`：coe_smul_finset (a : α) (s : Finset β) : ↑(a • s
) = a • (↑s : Set β)
· 使用定理 `Set.smul_set_subset_iff_subset_inv_smul_set`：smul_set_subset_iff_subset_
inv_smul_set : a • A subseteq B ↔ A subseteq a⁻¹ • B
-/
lemma smul_finset_subset_iff₀ (ha : a ≠ 0) : a • s ⊆ t ↔ s ⊆ a⁻¹ • t :=
  show Units.mk0 a ha • s ⊆ _ ↔ _ from smul_finset_subset_iff
/-
**Finset.subset_smul_finset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_smul_finset_iff : s subseteq a • t ↔ a⁻¹ • s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.coe_smul_finset`：coe_smul_finset (a : α) (s : Finset β) : ↑(a • s
) = a • (↑s : Set β)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.subset_smul_set_iff`：subset_smul_set_iff : A subseteq a • B ↔ a⁻¹ • 
A subseteq B
-/
lemma subset_smul_finset_iff₀ (ha : a ≠ 0) : s ⊆ a • t ↔ a⁻¹ • s ⊆ t :=
  show _ ⊆ Units.mk0 a ha • t ↔ _ from subset_smul_finset_iff
/-
**Finset.smul_finset_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：smul_finset_inter : a • (s inter t) = a • s inter a • t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_inter`：image_inter [DecidableEq α] (s₁ s₂ : Finset α) (hf :
 Injective f) : (s₁ inter s₂).image f = s₁.image f inter s₂.image f
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
-/
lemma smul_finset_inter₀ (ha : a ≠ 0) : a • (s ∩ t) = a • s ∩ a • t :=
  image_inter _ _ <| MulAction.injective₀ ha
/-
**Finset.smul_finset_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：smul_finset_sdiff : a • (s \ t) = a • s \ a • t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_sdiff`：image_sdiff [DecidableEq α] {f : α -> β} (s t : Fins
et α) (hf : Injective f) : (s \ t).image f = s.image f \ t.image f
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
-/
lemma smul_finset_sdiff₀ (ha : a ≠ 0) : a • (s \ t) = a • s \ a • t :=
  image_sdiff _ _ <| MulAction.injective₀ ha

open scoped symmDiff in
/-
**Finset.smul_finset_symmDiff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：smul_finset_symmDiff : a • s ∆ t = (a • s) ∆ (a • t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_symmDiff`：image_symmDiff [DecidableEq β] {f : α -> β} (s t 
: Finset α) (hf : Injective f) : (s ∆ t).image f = s.image f ∆ t.image f
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
-/
lemma smul_finset_symmDiff₀ (ha : a ≠ 0) : a • s ∆ t = (a • s) ∆ (a • t) :=
  image_symmDiff _ _ <| MulAction.injective₀ ha
/-
**Finset.smul_finset_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：smul_finset_univ [Fintype β] : a • (univ : Finset β) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_univ_of_surjective`：image_univ_of_surjective [Fintype β] {f
 : β -> α} (hf : Surjective f) : univ.image f = univ
· 使用定理 `MulAction.surjective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [
inst_1 : MulAction α β] (g : α), Function.Surjective fun x => g • x
-/
lemma smul_finset_univ₀ [Fintype β] (ha : a ≠ 0) : a • (univ : Finset β) = univ :=
  coe_injective <| by push_cast; exact Set.smul_set_univ₀ ha

@[simp]
/-
**Finset.smul_finset_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：smul_finset_eq_univ [Fintype β] : a • s = univ ↔ s = univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_eq_iff_eq_inv_smul`：smul_eq_iff_eq_inv_smul (g : α) {x y : β} : g •
 x = y ↔ x = g⁻¹ • y
· 使用定理 `Finset.smul_finset_univ`：smul_finset_univ [Fintype β] : a • (univ : Fins
et β) = univ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma smul_finset_eq_univ₀ [Fintype β] (ha : a ≠ 0) : a • s = univ ↔ s = univ := by
  exact_mod_cast smul_finset_eq_univ (α := Units α) (a := Units.mk0 a ha)
/-
**Finset.smul_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：smul_univ [Fintype β] {s : Finset α} (hs : s.Nonempty) : s • (univ : Finse
t β) = univ
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.coe_smul`：coe_smul (s : Finset α) (t : Finset β) : ↑(s • t) = (s 
: Set α) • (t : Set β)
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.smul_univ`：smul_univ {s : Set α} (hs : s.Nonempty) : s • (univ : Set
 β) = univ
-/
lemma smul_univ₀ [Fintype β] {s : Finset α} (hs : ¬s ⊆ 0) : s • (univ : Finset β) = univ :=
  coe_injective <| by
    rw [← coe_subset] at hs
    push_cast at hs ⊢
    exact Set.smul_univ₀ hs
/-
**Finset.smul_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：smul_univ [Fintype β] {s : Finset α} (hs : s.Nonempty) : s • (univ : Finse
t β) = univ
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.coe_smul`：coe_smul (s : Finset α) (t : Finset β) : ↑(s • t) = (s 
: Set α) • (t : Set β)
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.smul_univ`：smul_univ {s : Set α} (hs : s.Nonempty) : s • (univ : Set
 β) = univ
-/
lemma smul_univ₀' [Fintype β] {s : Finset α} (hs : s.Nontrivial) : s • (univ : Finset β) = univ :=
  coe_injective <| by push_cast; exact Set.smul_univ₀' hs

@[simp]
/-
**Finset.card_smul_finset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_smul_finset (a : α) (s : Finset β) : (a • s).card = s.card
参数：a : α；s : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_image_of_injective`：card_image_of_injective [DecidableEq β] 
(s : Finset α) (H : Injective f) : #(s.image f) = #s
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
-/
lemma card_smul_finset₀ (ha : a ≠ 0) (s : Finset β) : (a • s).card = s.card :=
  card_image_of_injective _ (MulAction.injective₀ ha)

/-- If the left cosets of `t` by elements of `s` are disjoint (but not necessarily distinct!), then
the size of `t` divides the size of `s • t`. -/
/-
**Finset.card_dvd_card_smul_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_dvd_card_smul_right {s : Finset α} : ((· • t) '' (s : Set α)).Pairwis
eDisjoint id -> t.card ∣ (s • t).card
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_dvd_card_image₂_right`：card_dvd_card_image₂_right (hf : fora
ll a in s, Injective (f a)) (hs : ((fun a => t.image <| f a) '' s).PairwiseDisjo
int id) : #t ∣ #(image₂…
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x

--- 原说明 ---
If the left cosets of `t` by elements of `s` are disjoint (but not necessarily d
istinct!), then
the size of `t` divides the size of `s • t`.
-/
lemma card_dvd_card_smul_right₀ {s : Finset α} (hs : ∀ a ∈ s, a ≠ 0) :
    ((· • t) '' (s : Set α)).PairwiseDisjoint id → t.card ∣ (s • t).card :=
  card_dvd_card_image₂_right fun a ha => MulAction.injective₀ (hs a ha)

end MulAction

variable [DecidableEq α] {s : Finset α}

open scoped RightActions

/-
**Finset.inv_smul_finset_distrib** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：inv_smul_finset_distrib (a : α) (s : Finset α) : (a • s)⁻¹ = op a⁻¹ • s⁻¹
参数：a : α；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma inv_smul_finset_distrib₀ (a : α) (s : Finset α) : (a • s)⁻¹ = s⁻¹ <• a⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [*]
  -- was `simp` and very slow (https://github.com/leanprover-community/mathlib4/issues/19751)
  · ext; simp only [mem_inv', ne_eq, not_false_eq_true, ← inv_smul_mem_iff₀, smul_eq_mul,
      MulOpposite.op_inv, inv_eq_zero, MulOpposite.op_eq_zero_iff, inv_inv,
      MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, mul_inv_rev, ha]
/-
**Finset.inv_op_smul_finset_distrib** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：inv_op_smul_finset_distrib (a : α) (s : Finset α) : (op a • s)⁻¹ = a⁻¹ • s
⁻¹
参数：a : α；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma inv_op_smul_finset_distrib₀ (a : α) (s : Finset α) : (s <• a)⁻¹ = a⁻¹ • s⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [*]
  -- was `simp` and very slow (https://github.com/leanprover-community/mathlib4/issues/19751)
  · ext; simp only [mem_inv', ne_eq, MulOpposite.op_eq_zero_iff, not_false_eq_true, ←
      inv_smul_mem_iff₀, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_inv, MulOpposite.unop_op,
      inv_eq_zero, inv_inv, smul_eq_mul, mul_inv_rev, ha]

end GroupWithZero

section Monoid
variable [Monoid α] [AddGroup β] [DistribMulAction α β]

@[simp]
/-
**Finset.smul_finset_neg** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：smul_finset_neg (a : α) (t : Finset β) : a • -t = -(a • t)
参数：a : α；t : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.image_image`：image_image [DecidableEq γ] {g : β -> γ} : (s.image 
f).image g = s.image (g ∘ f)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smul_finset_neg (a : α) (t : Finset β) : a • -t = -(a • t) := by
  simp only [← image_smul, ← image_neg_eq_neg, Function.comp_def, image_image, smul_neg]

@[simp]
/-
**Finset.smul_neg** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq β] [inst_1 : Monoid α]
 [inst_2 : AddGroup β]   [inst_3 : DistribMulAction α β] (s : Finset α) (t : Fin
set β), s • -t = -(s • t)
参数：s : Finset α；t : Finset β；s • t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_image₂_right_comm`：image_image₂_right_comm {f : α -> β' -> 
γ} {g : β -> β'} {f' : α -> β -> δ} {g' : δ -> γ} (h_right_comm : forall a b, f 
a (g b) = g' (f' a b…
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
-/
protected lemma smul_neg (s : Finset α) (t : Finset β) : s • -t = -(s • t) := by
  simp_rw [← image_neg_eq_neg]; exact image_image₂_right_comm smul_neg

end Monoid
end Finset

