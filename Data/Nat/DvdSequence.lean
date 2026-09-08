/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Action.Pi

/-!
# Divisibility sequences

A sequence `f : ℕ → ℕ` is a *divisibility sequence* if it satisfies `f a ∣ f b` whenever `a ∣ b`.

A sequence `f : ℕ → ℕ` is a *strong divisibility sequence* if `gcd (f a) (f b) = f (gcd a b)`.

This file defines divisibility sequences and strong divisibility sequences, and provides some basic
API for these definitions.

## Main definitions

* `IsDvdSeq`: A function `f` is a divisibility sequence if `a ∣ b` implies `f a ∣ f b`.
* `Nat.IsStrongDvdSeq`: A function `f : ℕ → ℕ` is a strong divisibility sequence if `f` satisfies
  `gcd (f a) (f b) = f (gcd a b)`.
-/

@[expose] public section

variable {α β γ : Type*}

-- this lemma regarding interaction between `smul` and `dvd` does not have a good home in mathlib
/-
**smul_dvd_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_dvd_smul [Monoid α] [Monoid β] [SMul α β] [IsScalarTower α β β] [IsSc
alarTower α α β] [SMulCommClass α β β] {a b : α} {c d : β} (hab : a ∣ b) (hcd : 
c ∣ d) : (a • c) ∣ (b • d)
参数：hab : a ∣ b；hcd : c ∣ d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mul_smul_mul_comm`：mul_smul_mul_comm [Mul α] [Mul β] [SMul α β] [IsScala
rTower α β β] [IsScalarTower α α β] [SMulCommClass α β β] (a b : α) (c d : β) : 
(a * b)…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma smul_dvd_smul [Monoid α] [Monoid β] [SMul α β] [IsScalarTower α β β]
    [IsScalarTower α α β] [SMulCommClass α β β] {a b : α} {c d : β}
    (hab : a ∣ b) (hcd : c ∣ d) : (a • c) ∣ (b • d) := by
  obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := hab, hcd
  exact ⟨x • y, mul_smul_mul_comm a x c y⟩

/-- A function `f : α → β` is a divisibility sequence if `a ∣ b` implies `f a ∣ f b`. -/
/-
**IsDvdSequence** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsDvdSequence [Dvd α] [Dvd β] (f : α -> β) : Prop
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : α → β` is a divisibility sequence if `a ∣ b` implies `f a ∣ f b`
.
-/
def IsDvdSequence [Dvd α] [Dvd β] (f : α → β) : Prop :=
  ∀ a b, a ∣ b → f a ∣ f b

@[deprecated (since := "2026-06-30")] alias IsDivSequence := IsDvdSequence

namespace IsDvdSequence

variable (α) in
/-
**IsDvdSequence.id** 是 Mathlib 中的一个定理，位于命名空间 `IsDvdSequence`。
形式化陈述：∀ (α : Type u_1) [inst : Dvd α], IsDvdSequence id
参数：α : Type u_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem id [Dvd α] : IsDvdSequence (id : α → α) :=
  fun _ _ ↦ id

variable (α) in
/-
**IsDvdSequence.const** 是 Mathlib 中的一个定理，位于命名空间 `IsDvdSequence`。
形式化陈述：∀ (α : Type u_1) {β : Type u_2} [inst : Dvd α] [inst_1 : Monoid β] (b : β)
, IsDvdSequence fun x => b
参数：α : Type u_1；b : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected theorem const [Dvd α] [Monoid β] (b : β) : IsDvdSequence (fun _ : α ↦ b) := by
  simp [IsDvdSequence]
/-
**IsDvdSequence.smul'** 是 Mathlib 中的一个定理，位于命名空间 `IsDvdSequence`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Dvd α] [inst_1 : Mo
noid β] [inst_2 : Monoid γ] {f : α → β}   {g : α → γ} [inst_3 : SMul β γ] [IsSca
larTower β γ γ] [IsScalarTower β β γ] [SMulCommClass β γ γ],   IsDvdSequence f →
 IsDvdSequence g → IsDvdSequence (f • g)
参数：f • g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_dvd_smul`：smul_dvd_smul [Monoid α] [Monoid β] [SMul α β] [IsScalarT
ower α β β] [IsScalarTower α α β] [SMulCommClass α β β] {a b : α} {c d : β} (hab
 : …
-/
protected theorem smul' [Dvd α] [Monoid β] [Monoid γ] {f : α → β} {g : α → γ} [SMul β γ]
    [IsScalarTower β γ γ] [IsScalarTower β β γ] [SMulCommClass β γ γ]
    (hf : IsDvdSequence f) (hg : IsDvdSequence g) : IsDvdSequence (f • g) :=
  fun a b hab ↦ smul_dvd_smul (hf a b hab) (hg a b hab)
/-
**IsDvdSequence.mul** 是 Mathlib 中的一个定理，位于命名空间 `IsDvdSequence`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Dvd α] [inst_1 : CommMonoid β] {f 
g : α → β},   IsDvdSequence f → IsDvdSequence g → IsDvdSequence (f * g)
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDvdSequence.smul'`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [ins
t : Dvd α] [inst_1 : Monoid β] [inst_2 : Monoid γ] {f : α → β}   {g : α → γ} [in
st_3 : SM…
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
-/
protected theorem mul [Dvd α] [CommMonoid β] {f g : α → β} (hf : IsDvdSequence f)
    (hg : IsDvdSequence g) : IsDvdSequence (f * g) :=
  .smul' hf hg
/-
**IsDvdSequence.smul** 是 Mathlib 中的一个定理，位于命名空间 `IsDvdSequence`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Dvd α] [inst_1 : Mo
noid β] [inst_2 : Monoid γ] {f : α → γ}   [inst_3 : SMul β γ] [IsScalarTower β γ
 γ] [IsScalarTower β β γ] [SMulCommClass β γ γ] (b : β),   IsDvdSequence f → IsD
vdSequence (b • f)
参数：b : β；b • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDvdSequence.smul'`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [ins
t : Dvd α] [inst_1 : Monoid β] [inst_2 : Monoid γ] {f : α → β}   {g : α → γ} [in
st_3 : SM…
· 使用定理 `IsDvdSequence.const`：∀ (α : Type u_1) {β : Type u_2} [inst : Dvd α] [ins
t_1 : Monoid β] (b : β), IsDvdSequence fun x => b
-/
protected theorem smul [Dvd α] [Monoid β] [Monoid γ] {f : α → γ} [SMul β γ] [IsScalarTower β γ γ]
    [IsScalarTower β β γ] [SMulCommClass β γ γ] (b : β) (hg : IsDvdSequence f) :
    IsDvdSequence (b • f) :=
  .smul' (.const α b) hg

end IsDvdSequence

@[deprecated (since := "2026-06-30")] alias IsDivSequence.smul := IsDvdSequence.smul
@[deprecated (since := "2026-06-30")] alias isDivSequence_id := IsDvdSequence.id

namespace Nat

/-- A function `f : ℕ → ℕ` is a strong divisibility sequence if `gcd (f a) (f b) = f (gcd a b)`. -/
/-
**Nat.IsStrongDvdSequence** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：IsStrongDvdSequence (f : Nat -> Nat) : Prop
参数：f : Nat -> Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : ℕ → ℕ` is a strong divisibility sequence if `gcd (f a) (f b) = f
 (gcd a b)`.
-/
def IsStrongDvdSequence (f : ℕ → ℕ) : Prop :=
  ∀ a b, (f a).gcd (f b) = f (a.gcd b)

namespace IsStrongDvdSequence

/-
**Nat.IsStrongDvdSequence.isDvdSequence** 是 Mathlib 中的一个定理，位于命名空间 `Nat.IsStrongD
vdSequence`。
形式化陈述：isDvdSequence {f : Nat -> Nat} (hf : IsStrongDvdSequence f) : IsDvdSequenc
e f
参数：hf : IsStrongDvdSequence f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.gcd_eq_left`：∀ {m n : ℕ}, m ∣ n → m.gcd n = m
-/
theorem isDvdSequence {f : ℕ → ℕ} (hf : IsStrongDvdSequence f) : IsDvdSequence f := by
  intro a b hab
  simpa [gcd_eq_left hab, gcd_eq_left_iff_dvd] using hf a b
/-
**Nat.IsStrongDvdSequence.id** 是 Mathlib 中的一个定理，位于命名空间 `Nat.IsStrongDvdSequence`
。
形式化陈述：Nat.IsStrongDvdSequence id
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem id : IsStrongDvdSequence (id : ℕ → ℕ) :=
  fun _ _ ↦ rfl
/-
**Nat.IsStrongDvdSequence.const** 是 Mathlib 中的一个定理，位于命名空间 `Nat.IsStrongDvdSequen
ce`。
形式化陈述：∀ (n : ℕ), Nat.IsStrongDvdSequence fun x => n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.gcd_self`：∀ (n : ℕ), n.gcd n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected theorem const (n : ℕ) : IsStrongDvdSequence (fun _ ↦ n) := by
  simp [IsStrongDvdSequence]

end IsStrongDvdSequence

end Nat

