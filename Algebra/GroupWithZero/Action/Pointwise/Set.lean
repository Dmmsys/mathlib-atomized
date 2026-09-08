/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.GroupWithZero.Pointwise.Set.Basic

/-!
# Pointwise operations of sets in a group with zero

This file proves properties of pointwise operations of sets in a group with zero.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

@[expose] public section

assert_not_exists IsOrderedMonoid Ring

open Function
open scoped Pointwise

variable {α β : Type*}

namespace Set

/-
**Set.smul_set_pi** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_set_pi {G ι : Type*} {α : ι -> Type*} [Group G] [forall i, MulAction 
G (α i)] (c : G) (I : Set ι) (s : forall i, Set (α i)) : c • I.pi s = I.pi (c • 
s)
参数：α i；c : G；I : Set ι；s : forall i, Set (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_set_pi_of_surjective`：smul_set_pi_of_surjective (c : M) (I : Se
t ι) (s : forall i, Set (π i)) (hsurj : forall i ∉ I, Function.Surjective (c • ·
 : π i -> π i)) : c…
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `MulAction.bijective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Bijective fun x => g • x
-/
lemma smul_set_pi₀ {M ι : Type*} {α : ι → Type*} [GroupWithZero M] [∀ i, MulAction M (α i)]
    {c : M} (hc : c ≠ 0) (I : Set ι) (s : ∀ i, Set (α i)) : c • I.pi s = I.pi (c • s) :=
  smul_set_pi_of_isUnit (.mk0 _ hc) I s

/-- A slightly more general version of `Set.smul_set_pi₀`. -/
/-
**Set.smul_set_pi** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_set_pi {G ι : Type*} {α : ι -> Type*} [Group G] [forall i, MulAction 
G (α i)] (c : G) (I : Set ι) (s : forall i, Set (α i)) : c • I.pi s = I.pi (c • 
s)
参数：α i；c : G；I : Set ι；s : forall i, Set (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_set_pi_of_surjective`：smul_set_pi_of_surjective (c : M) (I : Se
t ι) (s : forall i, Set (π i)) (hsurj : forall i ∉ I, Function.Surjective (c • ·
 : π i -> π i)) : c…
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `MulAction.bijective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Bijective fun x => g • x

--- 原说明 ---
A slightly more general version of `Set.smul_set_pi₀`.
-/
lemma smul_set_pi₀' {M ι : Type*} {α : ι → Type*} [GroupWithZero M] [∀ i, MulAction M (α i)]
    {c : M} {I : Set ι} (h : c ≠ 0 ∨ I = univ) (s : ∀ i, Set (α i)) : c • I.pi s = I.pi (c • s) :=
  h.elim (fun hc ↦ smul_set_pi_of_isUnit (.mk0 _ hc) I s) (fun hI ↦ hI ▸ smul_set_univ_pi ..)

section SMulZeroClass
variable [Zero β] [SMulZeroClass α β] {s : Set α} {t : Set β} {a : α}

/-- If scalar multiplication by elements of `α` sends `(0 : β)` to zero,
then the same is true for `(0 : Set β)`. -/
@[instance_reducible]
/-
**Set.smulZeroClassSet** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [inst : Zero β] → [SMulZeroClass α β] → 
SMulZeroClass α (Set β)
参数：Set β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If scalar multiplication by elements of `α` sends `(0 : β)` to zero,
then the same is true for `(0 : Set β)`.
-/
protected def smulZeroClassSet : SMulZeroClass α (Set β) where
  smul_zero _ := image_singleton.trans <| by rw [smul_zero, singleton_zero]

scoped[Pointwise] attribute [instance] Set.smulZeroClassSet
/-
**Set.smul_zero_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_zero_subset (s : Set α) : s • (0 : Set β) subseteq 0
参数：s : Set α。
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
lemma smul_zero_subset (s : Set α) : s • (0 : Set β) ⊆ 0 := by simp [subset_def, mem_smul]
/-
**Set.Nonempty.smul_zero** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Zero β] [inst_1 : SMulZeroClass α 
β] {s : Set α}, s.Nonempty → s • 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `Set.smul_zero_subset`：smul_zero_subset (s : Set α) : s • (0 : Set β) sub
seteq 0
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
lemma Nonempty.smul_zero (hs : s.Nonempty) : s • (0 : Set β) = 0 :=
  s.smul_zero_subset.antisymm <| by simpa [mem_smul] using! hs
/-
**Set.zero_mem_smul_set** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：zero_mem_smul_set (h : (0 : β) in t) : (0 : β) in a • t
参数：h : (0 : β) in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
lemma zero_mem_smul_set (h : (0 : β) ∈ t) : (0 : β) ∈ a • t := ⟨0, h, smul_zero _⟩

end SMulZeroClass
section SMulWithZero

variable [Zero α] [Zero β] [SMulWithZero α β] {s : Set α} {t : Set β}

/-!
Note that we have neither `SMulWithZero α (Set β)` nor `SMulWithZero (Set α) (Set β)`
because `0 * ∅ ≠ 0`.
-/

/-
**Set.zero_smul_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：zero_smul_subset (t : Set β) : (0 : Set α) • t subseteq 0
参数：t : Set β。
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
Note that we have neither `SMulWithZero α (Set β)` nor `SMulWithZero (Set α) (Se
t β)`
because `0 * ∅ ≠ 0`.
-/
lemma zero_smul_subset (t : Set β) : (0 : Set α) • t ⊆ 0 := by simp [subset_def, mem_smul]
/-
**Set.Nonempty.zero_smul** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Zero α] [inst_1 : Zero β] [inst_2 
: SMulWithZero α β] {t : Set β},   t.Nonempty → 0 • t = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `Set.zero_smul_subset`：zero_smul_subset (t : Set β) : (0 : Set α) • t sub
seteq 0
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
lemma Nonempty.zero_smul (ht : t.Nonempty) : (0 : Set α) • t = 0 :=
  t.zero_smul_subset.antisymm <| by simpa [mem_smul] using! ht

/-- A nonempty set is scaled by zero to the singleton set containing 0. -/
/-
**Set.zero_smul_set** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Zero α] [inst_1 : Zero β] [inst_2 
: SMulWithZero α β] {s : Set β},   s.Nonempty → 0 • s = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Set.Nonempty.image_const`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s
.Nonempty → ∀ (a : β), (fun x => a) '' s = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A nonempty set is scaled by zero to the singleton set containing 0.
-/
@[simp] lemma zero_smul_set {s : Set β} (h : s.Nonempty) : (0 : α) • s = (0 : Set β) := by
  simp only [← image_smul, zero_smul, h.image_const, singleton_zero]
/-
**Set.zero_smul_set_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：zero_smul_set_subset (s : Set β) : (0 : α) • s subseteq 0
参数：s : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
lemma zero_smul_set_subset (s : Set β) : (0 : α) • s ⊆ 0 :=
  image_subset_iff.2 fun x _ ↦ zero_smul α x
/-
**Set.subsingleton_zero_smul_set** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：subsingleton_zero_smul_set (s : Set β) : ((0 : α) • s).Subsingleton
参数：s : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.anti`：∀ {α : Type u} {s t : Set α}, t.Subsingleton → s 
⊆ t → s.Subsingleton
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton
· 使用引理 `Set.zero_smul_set_subset`：zero_smul_set_subset (s : Set β) : (0 : α) • s
 subseteq 0
-/
lemma subsingleton_zero_smul_set (s : Set β) : ((0 : α) • s).Subsingleton :=
  subsingleton_singleton.anti <| zero_smul_set_subset s

end SMulWithZero

/-- If the scalar multiplication `(· • ·) : α → β → β` is distributive,
then so is `(· • ·) : α → Set β → Set β`. -/
@[instance_reducible]
/-
**Set.distribSMulSet** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [inst : AddZeroClass β] → [DistribSMul α
 β] → DistribSMul α (Set β)
参数：Set β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the scalar multiplication `(· • ·) : α → β → β` is distributive,
then so is `(· • ·) : α → Set β → Set β`.
-/
protected noncomputable def distribSMulSet [AddZeroClass β] [DistribSMul α β] :
    DistribSMul α (Set β) where
  smul_add _ _ _ := image_image2_distrib <| smul_add _

scoped[Pointwise] attribute [instance] Set.distribSMulSet

/-- A distributive multiplicative action of a monoid on an additive monoid `β` gives a distributive
multiplicative action on `Set β`. -/
@[instance_reducible]
/-
**Set.distribMulActionSet** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} → [inst : Monoid α] → [inst_1 : AddMonoi
d β] → [DistribMulAction α β] → DistribMulAction α (Set β)
参数：Set β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A distributive multiplicative action of a monoid on an additive monoid `β` gives
 a distributive
multiplicative action on `Set β`.
-/
protected noncomputable def distribMulActionSet [Monoid α] [AddMonoid β] [DistribMulAction α β] :
    DistribMulAction α (Set β) where
  smul_add := smul_add
  smul_zero := smul_zero

/-- A multiplicative action of a monoid on a monoid `β` gives a multiplicative action on `Set β`. -/
@[instance_reducible]
/-
**Set.mulDistribMulActionSet** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} → [inst : Monoid α] → [inst_1 : Monoid β
] → [MulDistribMulAction α β] → MulDistribMulAction α (Set β)
参数：Set β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A multiplicative action of a monoid on a monoid `β` gives a multiplicative actio
n on `Set β`.
-/
protected noncomputable def mulDistribMulActionSet [Monoid α] [Monoid β] [MulDistribMulAction α β] :
    MulDistribMulAction α (Set β) where
  smul_mul _ _ _ := image_image2_distrib <| smul_mul' _
  smul_one _ := image_singleton.trans <| by rw [smul_one, singleton_one]

scoped[Pointwise] attribute [instance] Set.distribMulActionSet Set.mulDistribMulActionSet
/-
**Set.** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors (Set α) where
  eq_zero_or_eq_zero_of_mul_eq_zero {s t} h := by
    by_contra! H
    have hst : (s * t).Nonempty := h.symm.subst zero_nonempty
    rw [Ne, ← hst.of_smul_left.subset_zero_iff, Ne, ← hst.of_smul_right.subset_zero_iff] at H
    simp only [not_subset, mem_zero] at H
    obtain ⟨⟨a, hs, ha⟩, b, ht, hb⟩ := H
    exact (eq_zero_or_eq_zero_of_mul_eq_zero <| h.subset <| mul_mem_mul hs ht).elim ha hb

section GroupWithZero
variable [GroupWithZero α] [MulAction α β] {s t : Set β} {a : α}

@[simp]
/-
**Set.smul_mem_smul_set_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：smul_mem_smul_set_iff : a • x in a • s ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
-/
lemma smul_mem_smul_set_iff₀ (ha : a ≠ 0) (A : Set β) (x : β) : a • x ∈ a • A ↔ x ∈ A :=
  show Units.mk0 a ha • _ ∈ _ ↔ _ from smul_mem_smul_set_iff
/-
**Set.mem_smul_set_iff_inv_smul_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_smul_set_iff_inv_smul_mem : x in a • A ↔ a⁻¹ • x in A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_equiv`：∀ {α : Type u_3} {β : Type u_4} {S : Set α} {f : α 
≃ β} {x : β}, x ∈ ⇑f '' S ↔ f.symm x ∈ S
-/
lemma mem_smul_set_iff_inv_smul_mem₀ (ha : a ≠ 0) (A : Set β) (x : β) : x ∈ a • A ↔ a⁻¹ • x ∈ A :=
  show _ ∈ Units.mk0 a ha • _ ↔ _ from mem_smul_set_iff_inv_smul_mem
/-
**Set.mem_inv_smul_set_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_inv_smul_set_iff : x in a⁻¹ • A ↔ a • x in A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_inv_smul_set_iff₀ (ha : a ≠ 0) (A : Set β) (x : β) : x ∈ a⁻¹ • A ↔ a • x ∈ A :=
  show _ ∈ (Units.mk0 a ha)⁻¹ • _ ↔ _ from mem_inv_smul_set_iff
/-
**Set.preimage_smul** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_smul (a : α) (t : Set β) : (fun x => a • x) ⁻¹' t = a⁻¹ • t
参数：a : α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Equiv.image_symm_eq_preimage`：image_symm_eq_preimage (e : α ≃ β) (s : Se
t β) : e.symm '' s = e ⁻¹' s
-/
lemma preimage_smul₀ (ha : a ≠ 0) (t : Set β) : (fun x ↦ a • x) ⁻¹' t = a⁻¹ • t :=
  preimage_smul (Units.mk0 a ha) t
/-
**Set.preimage_smul_inv** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_smul_inv (a : α) (t : Set β) : (fun x => a⁻¹ • x) ⁻¹' t = a • t
参数：a : α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_smul`：preimage_smul (a : α) (t : Set β) : (fun x => a • x) 
⁻¹' t = a⁻¹ • t
-/
lemma preimage_smul_inv₀ (ha : a ≠ 0) (t : Set β) : (fun x ↦ a⁻¹ • x) ⁻¹' t = a • t :=
  preimage_smul (Units.mk0 a ha)⁻¹ t

@[simp]
/-
**Set.smul_set_subset_smul_set_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：smul_set_subset_smul_set_iff : a • A subseteq a • B ↔ A subseteq B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_image_iff`：image_subset_image_iff {f : α -> β} (hf : In
jective f) : f '' s subseteq f '' t ↔ s subseteq t
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
-/
lemma smul_set_subset_smul_set_iff₀ (ha : a ≠ 0) {A B : Set β} : a • A ⊆ a • B ↔ A ⊆ B :=
  show Units.mk0 a ha • A ⊆ _ ↔ _ from smul_set_subset_smul_set_iff
/-
**Set.smul_set_subset_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_set_subset_iff : a • s subseteq t ↔ forall ⦃b⦄, b in s -> a • b in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
lemma smul_set_subset_iff₀ (ha : a ≠ 0) {A B : Set β} : a • A ⊆ B ↔ A ⊆ a⁻¹ • B :=
  show Units.mk0 a ha • A ⊆ _ ↔ _ from smul_set_subset_iff_subset_inv_smul_set
/-
**Set.subset_smul_set_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_smul_set_iff : A subseteq a • B ↔ a⁻¹ • A subseteq B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
lemma subset_smul_set_iff₀ (ha : a ≠ 0) {A B : Set β} : A ⊆ a • B ↔ a⁻¹ • A ⊆ B :=
  show _ ⊆ Units.mk0 a ha • B ↔ _ from subset_smul_set_iff
/-
**Set.smul_set_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：smul_set_inter : a • (s inter t) = a • s inter a • t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_inter`：image_inter {f : α -> β} {s t : Set α} (H : Injective f
) : f '' (s inter t) = f '' s inter f '' t
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
-/
lemma smul_set_inter₀ (ha : a ≠ 0) : a • (s ∩ t) = a • s ∩ a • t :=
  show Units.mk0 a ha • _ = _ from smul_set_inter
/-
**Set.smul_set_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：smul_set_sdiff : a • (s \ t) = a • s \ a • t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_sdiff`：image_sdiff {f : α -> β} (hf : Injective f) (s t : Set 
α) : f '' (s \ t) = f '' s \ f '' t
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
-/
lemma smul_set_sdiff₀ (ha : a ≠ 0) : a • (s \ t) = a • s \ a • t :=
  image_sdiff (MulAction.injective₀ ha) _ _

open scoped symmDiff in
/-
**Set.smul_set_symmDiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：smul_set_symmDiff : a • s ∆ t = (a • s) ∆ (a • t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_symmDiff`：image_symmDiff (hf : Injective f) (s t : Set α) : f 
'' s ∆ t = (f '' s) ∆ (f '' t)
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
-/
lemma smul_set_symmDiff₀ (ha : a ≠ 0) : a • s ∆ t = (a • s) ∆ (a • t) :=
  image_symmDiff (MulAction.injective₀ ha) _ _
/-
**Set.smul_set_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：smul_set_univ : a • (univ : Set β) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_univ_of_surjective`：image_univ_of_surjective {ι : Type*} {f : 
ι -> β} (H : Surjective f) : f '' univ = univ
· 使用定理 `MulAction.surjective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [
inst_1 : MulAction α β] (g : α), Function.Surjective fun x => g • x
-/
lemma smul_set_univ₀ (ha : a ≠ 0) : a • (univ : Set β) = univ :=
  image_univ_of_surjective <| MulAction.surjective₀ ha
/-
**Set.smul_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：smul_univ {s : Set α} (hs : s.Nonempty) : s • (univ : Set β) = univ
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `trivial`：True
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
-/
lemma smul_univ₀ {s : Set α} (hs : ¬s ⊆ 0) : s • (univ : Set β) = univ :=
  let ⟨a, ha, ha₀⟩ := not_subset.1 hs
  eq_univ_of_forall fun b ↦ ⟨a, ha, a⁻¹ • b, trivial, smul_inv_smul₀ ha₀ _⟩
/-
**Set.smul_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：smul_univ {s : Set α} (hs : s.Nonempty) : s • (univ : Set β) = univ
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `trivial`：True
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
-/
lemma smul_univ₀' {s : Set α} (hs : s.Nontrivial) : s • (univ : Set β) = univ :=
  smul_univ₀ hs.not_subset_singleton

open scoped RightActions in
/-
**Set.inv_smul_set_distrib** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：inv_smul_set_distrib (a : α) (s : Set α) : (a • s)⁻¹ = op a⁻¹ • s⁻¹
参数：a : α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
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
@[simp] lemma inv_smul_set_distrib₀ (a : α) (s : Set α) : (a • s)⁻¹ = s⁻¹ <• a⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [*]
  · ext; simp [mem_smul_set_iff_inv_smul_mem₀, *]

open scoped RightActions in
/-
**Set.inv_op_smul_set_distrib** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：inv_op_smul_set_distrib (a : α) (s : Set α) : (op a • s)⁻¹ = a⁻¹ • s⁻¹
参数：a : α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
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
@[simp] lemma inv_op_smul_set_distrib₀ (a : α) (s : Set α) : (s <• a)⁻¹ = a⁻¹ • s⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [*]
  · ext; simp [mem_smul_set_iff_inv_smul_mem₀, *]

end GroupWithZero
end Set

