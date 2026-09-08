/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Results about `CovariantClass G α HSMul.hSMul LE.le`

When working with group actions rather than modules, we drop the `0 < c` condition.

Notably these are relevant for pointwise actions on set-like objects.
-/

public section

variable {ι : Sort*} {M α : Type*}

/-
**smul_mono_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_mono_right [SMul M α] [Preorder α] [CovariantClass M α HSMul.hSMul LE
.le] (m : M) : Monotone (HSMul.hSMul m : α -> α)
参数：m : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N} {r 
: N → N → Prop} [self : CovariantClass M N μ r], Covariant M N μ r
-/
theorem smul_mono_right [SMul M α] [Preorder α] [CovariantClass M α HSMul.hSMul LE.le]
    (m : M) : Monotone (HSMul.hSMul m : α → α) :=
  fun _ _ => CovariantClass.elim _

/-- A copy of `smul_mono_right` that is understood by `gcongr`. -/
@[gcongr]
/-
**smul_le_smul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_le_smul_left [SMul M α] [Preorder α] [CovariantClass M α HSMul.hSMul 
LE.le] (m : M) {a b : α} (h : a <= b) : m • a <= m • b
参数：m : M；h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_mono_right`：smul_mono_right [SMul M α] [Preorder α] [CovariantClass
 M α HSMul.hSMul LE.le] (m : M) : Monotone (HSMul.hSMul m : α -> α)

--- 原说明 ---
A copy of `smul_mono_right` that is understood by `gcongr`.
-/
theorem smul_le_smul_left [SMul M α] [Preorder α] [CovariantClass M α HSMul.hSMul LE.le]
    (m : M) {a b : α} (h : a ≤ b) :
    m • a ≤ m • b :=
  smul_mono_right _ h
/-
**smul_inf_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_inf_le [SMul M α] [SemilatticeInf α] [CovariantClass M α HSMul.hSMul 
LE.le] (m : M) (a₁ a₂ : α) : m • (a₁ ⊓ a₂) <= m • a₁ ⊓ m • a₂
参数：m : M；a₁ a₂ : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_inf_le`：∀ {α : Type u} {β : Type v} [inst : SemilatticeInf 
α] [inst_1 : SemilatticeInf β] {f : α → β},   Monotone f → ∀ (x y : α), f (x ⊓ y
) ≤ f x ⊓…
· 使用定理 `smul_mono_right`：smul_mono_right [SMul M α] [Preorder α] [CovariantClass
 M α HSMul.hSMul LE.le] (m : M) : Monotone (HSMul.hSMul m : α -> α)
-/
theorem smul_inf_le [SMul M α] [SemilatticeInf α] [CovariantClass M α HSMul.hSMul LE.le]
    (m : M) (a₁ a₂ : α) : m • (a₁ ⊓ a₂) ≤ m • a₁ ⊓ m • a₂ :=
  (smul_mono_right _).map_inf_le _ _
/-
**smul_iInf_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_iInf_le [SMul M α] [CompleteLattice α] [CovariantClass M α HSMul.hSMu
l LE.le] {m : M} {t : ι -> α} : m • iInf t <= ⨅ i, m • t i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `smul_mono_right`：smul_mono_right [SMul M α] [Preorder α] [CovariantClass
 M α HSMul.hSMul LE.le] (m : M) : Monotone (HSMul.hSMul m : α -> α)
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
-/
theorem smul_iInf_le [SMul M α] [CompleteLattice α] [CovariantClass M α HSMul.hSMul LE.le]
    {m : M} {t : ι → α} :
    m • iInf t ≤ ⨅ i, m • t i :=
  le_iInf fun _ => smul_mono_right _ (iInf_le _ _)
/-
**smul_strictMono_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_strictMono_right [SMul M α] [Preorder α] [CovariantClass M α HSMul.hS
Mul LT.lt] (m : M) : StrictMono (HSMul.hSMul m : α -> α)
参数：m : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N} {r 
: N → N → Prop} [self : CovariantClass M N μ r], Covariant M N μ r
-/
theorem smul_strictMono_right [SMul M α] [Preorder α] [CovariantClass M α HSMul.hSMul LT.lt]
    (m : M) : StrictMono (HSMul.hSMul m : α → α) :=
  fun _ _ => CovariantClass.elim _
/-
**le_pow_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_pow_smul {G : Type*} [Monoid G] {α : Type*} [Preorder α] {g : G} {a : α
} [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le] (h : a <= g • a) (n : N
at) : a <= g ^ n • a
参数：h : a <= g • a；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `smul_mono_right`：smul_mono_right [SMul M α] [Preorder α] [CovariantClass
 M α HSMul.hSMul LE.le] (m : M) : Monotone (HSMul.hSMul m : α -> α)
-/
lemma le_pow_smul {G : Type*} [Monoid G] {α : Type*} [Preorder α] {g : G} {a : α}
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le]
    (h : a ≤ g • a) (n : ℕ) : a ≤ g ^ n • a := by
  induction n with
  | zero => rw [pow_zero, one_smul]
  | succ n hn =>
    rw [pow_succ', mul_smul]
    exact h.trans (smul_mono_right g hn)
/-
**pow_smul_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_smul_le {G : Type*} [Monoid G] {α : Type*} [Preorder α] {g : G} {a : α
} [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le] (h : g • a <= a) (n : N
at) : g ^ n • a <= a
参数：h : g • a <= a；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `smul_mono_right`：smul_mono_right [SMul M α] [Preorder α] [CovariantClass
 M α HSMul.hSMul LE.le] (m : M) : Monotone (HSMul.hSMul m : α -> α)
-/
lemma pow_smul_le {G : Type*} [Monoid G] {α : Type*} [Preorder α] {g : G} {a : α}
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le]
    (h : g • a ≤ a) (n : ℕ) : g ^ n • a ≤ a := by
  induction n with
  | zero => rw [pow_zero, one_smul]
  | succ n hn =>
    rw [pow_succ', mul_smul]
    exact (smul_mono_right g hn).trans h
