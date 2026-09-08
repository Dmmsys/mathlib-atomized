/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Lattice

/-!
# Monovariance of functions

Two functions *vary together* if a strict change in the first implies a change in the second.

This is in some sense a way to say that two functions `f : ι → α`, `g : ι → β` are "monotone
together", without actually having an order on `ι`.

This condition comes up in the rearrangement inequality. See `Algebra.Order.Rearrangement`.

## Main declarations

* `Monovary f g`: `f` monovaries with `g`. If `g i < g j`, then `f i ≤ f j`.
* `Antivary f g`: `f` antivaries with `g`. If `g i < g j`, then `f j ≤ f i`.
* `MonovaryOn f g s`: `f` monovaries with `g` on `s`.
* `AntivaryOn f g s`: `f` antivaries with `g` on `s`.
-/

@[expose] public section


open Function Set

variable {ι ι' α β γ : Type*}

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] {f : ι → α} {f' : α → γ} {g : ι → β}
  {s t : Set ι}

/-- `f` monovaries with `g` if `g i < g j` implies `f i ≤ f j`. -/
/-
**Monovary** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Monovary (f : ι -> α) (g : ι -> β) : Prop
参数：f : ι -> α；g : ι -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` monovaries with `g` if `g i < g j` implies `f i ≤ f j`.
-/
def Monovary (f : ι → α) (g : ι → β) : Prop :=
  ∀ ⦃i j⦄, g i < g j → f i ≤ f j

/-- `f` antivaries with `g` if `g i < g j` implies `f j ≤ f i`. -/
/-
**Antivary** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Antivary (f : ι -> α) (g : ι -> β) : Prop
参数：f : ι -> α；g : ι -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` antivaries with `g` if `g i < g j` implies `f j ≤ f i`.
-/
def Antivary (f : ι → α) (g : ι → β) : Prop :=
  ∀ ⦃i j⦄, g i < g j → f j ≤ f i

/-- `f` monovaries with `g` on `s` if `g i < g j` implies `f i ≤ f j` for all `i, j ∈ s`. -/
/-
**MonovaryOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MonovaryOn (f : ι -> α) (g : ι -> β) (s : Set ι) : Prop
参数：f : ι -> α；g : ι -> β；s : Set ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` monovaries with `g` on `s` if `g i < g j` implies `f i ≤ f j` for all `i, j 
∈ s`.
-/
def MonovaryOn (f : ι → α) (g : ι → β) (s : Set ι) : Prop :=
  ∀ ⦃i⦄ (_ : i ∈ s) ⦃j⦄ (_ : j ∈ s), g i < g j → f i ≤ f j

/-- `f` antivaries with `g` on `s` if `g i < g j` implies `f j ≤ f i` for all `i, j ∈ s`. -/
/-
**AntivaryOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AntivaryOn (f : ι -> α) (g : ι -> β) (s : Set ι) : Prop
参数：f : ι -> α；g : ι -> β；s : Set ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` antivaries with `g` on `s` if `g i < g j` implies `f j ≤ f i` for all `i, j 
∈ s`.
-/
def AntivaryOn (f : ι → α) (g : ι → β) (s : Set ι) : Prop :=
  ∀ ⦃i⦄ (_ : i ∈ s) ⦃j⦄ (_ : j ∈ s), g i < g j → f j ≤ f i
/-
**Monovary.monovaryOn** 是 Mathlib 中的一个定理，位于命名空间 `Monovary`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst : Preorder α] [inst_1
 : Preorder β] {f : ι → α} {g : ι → β},   Monovary f g → ∀ (s : Set ι), Monovary
On f g s
参数：s : Set ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Monovary.monovaryOn (h : Monovary f g) (s : Set ι) : MonovaryOn f g s :=
  fun _ _ _ _ hij => h hij
/-
**Antivary.antivaryOn** 是 Mathlib 中的一个定理，位于命名空间 `Antivary`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst : Preorder α] [inst_1
 : Preorder β] {f : ι → α} {g : ι → β},   Antivary f g → ∀ (s : Set ι), Antivary
On f g s
参数：s : Set ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Antivary.antivaryOn (h : Antivary f g) (s : Set ι) : AntivaryOn f g s :=
  fun _ _ _ _ hij => h hij

@[simp]
/-
**MonovaryOn.empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonovaryOn.empty : MonovaryOn f g ∅
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MonovaryOn.empty : MonovaryOn f g ∅ := fun _ => False.elim

@[simp]
/-
**AntivaryOn.empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntivaryOn.empty : AntivaryOn f g ∅
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AntivaryOn.empty : AntivaryOn f g ∅ := fun _ => False.elim

@[simp]
/-
**monovaryOn_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monovaryOn_univ : MonovaryOn f g univ ↔ Monovary f g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
theorem monovaryOn_univ : MonovaryOn f g univ ↔ Monovary f g :=
  ⟨fun h _ _ => h trivial trivial, fun h _ _ _ _ hij => h hij⟩

@[simp]
/-
**antivaryOn_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antivaryOn_univ : AntivaryOn f g univ ↔ Antivary f g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
theorem antivaryOn_univ : AntivaryOn f g univ ↔ Antivary f g :=
  ⟨fun h _ _ => h trivial trivial, fun h _ _ _ _ hij => h hij⟩
/-
**monovaryOn_iff_monovary** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monovaryOn_iff_monovary : MonovaryOn f g s ↔ Monovary (fun i : s => f i) f
un i => g i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma monovaryOn_iff_monovary : MonovaryOn f g s ↔ Monovary (fun i : s ↦ f i) fun i ↦ g i := by
  simp [Monovary, MonovaryOn]
/-
**antivaryOn_iff_antivary** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antivaryOn_iff_antivary : AntivaryOn f g s ↔ Antivary (fun i : s => f i) f
un i => g i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma antivaryOn_iff_antivary : AntivaryOn f g s ↔ Antivary (fun i : s ↦ f i) fun i ↦ g i := by
  simp [Antivary, AntivaryOn]
/-
**MonovaryOn.subset** 是 Mathlib 中的一个定理，位于命名空间 `MonovaryOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst : Preorder α] [inst_1
 : Preorder β] {f : ι → α} {g : ι → β}   {s t : Set ι}, s ⊆ t → MonovaryOn f g t
 → MonovaryOn f g s
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem MonovaryOn.subset (hst : s ⊆ t) (h : MonovaryOn f g t) : MonovaryOn f g s :=
  fun _ hi _ hj => h (hst hi) (hst hj)
/-
**AntivaryOn.subset** 是 Mathlib 中的一个定理，位于命名空间 `AntivaryOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst : Preorder α] [inst_1
 : Preorder β] {f : ι → α} {g : ι → β}   {s t : Set ι}, s ⊆ t → AntivaryOn f g t
 → AntivaryOn f g s
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem AntivaryOn.subset (hst : s ⊆ t) (h : AntivaryOn f g t) : AntivaryOn f g s :=
  fun _ hi _ hj => h (hst hi) (hst hj)
/-
**monovary_const_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monovary_const_left (g : ι -> β) (a : α) : Monovary (const ι a) g
参数：g : ι -> β；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem monovary_const_left (g : ι → β) (a : α) : Monovary (const ι a) g := fun _ _ _ => le_rfl
/-
**antivary_const_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antivary_const_left (g : ι -> β) (a : α) : Antivary (const ι a) g
参数：g : ι -> β；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem antivary_const_left (g : ι → β) (a : α) : Antivary (const ι a) g := fun _ _ _ => le_rfl
/-
**monovary_const_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monovary_const_right (f : ι -> α) (b : β) : Monovary f (const ι b)
参数：f : ι -> α；b : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
theorem monovary_const_right (f : ι → α) (b : β) : Monovary f (const ι b) := fun _ _ h =>
  (h.ne rfl).elim
/-
**antivary_const_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antivary_const_right (f : ι -> α) (b : β) : Antivary f (const ι b)
参数：f : ι -> α；b : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
theorem antivary_const_right (f : ι → α) (b : β) : Antivary f (const ι b) := fun _ _ h =>
  (h.ne rfl).elim
/-
**monovary_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monovary_self (f : ι -> α) : Monovary f f
参数：f : ι -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem monovary_self (f : ι → α) : Monovary f f := fun _ _ => le_of_lt
/-
**monovaryOn_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monovaryOn_self (f : ι -> α) (s : Set ι) : MonovaryOn f f s
参数：f : ι -> α；s : Set ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem monovaryOn_self (f : ι → α) (s : Set ι) : MonovaryOn f f s := fun _ _ _ _ => le_of_lt
/-
**Subsingleton.monovary** 是 Mathlib 中的一个定理，位于命名空间 `Subsingleton`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst : Preorder α] [inst_1
 : Preorder β] [Subsingleton ι] (f : ι → α)   (g : ι → β), Monovary f g
参数：f : ι → α；g : ι → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
protected theorem Subsingleton.monovary [Subsingleton ι] (f : ι → α) (g : ι → β) : Monovary f g :=
  fun _ _ h => (ne_of_apply_ne _ h.ne <| Subsingleton.elim _ _).elim
/-
**Subsingleton.antivary** 是 Mathlib 中的一个定理，位于命名空间 `Subsingleton`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst : Preorder α] [inst_1
 : Preorder β] [Subsingleton ι] (f : ι → α)   (g : ι → β), Antivary f g
参数：f : ι → α；g : ι → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
protected theorem Subsingleton.antivary [Subsingleton ι] (f : ι → α) (g : ι → β) : Antivary f g :=
  fun _ _ h => (ne_of_apply_ne _ h.ne <| Subsingleton.elim _ _).elim
/-
**Subsingleton.monovaryOn** 是 Mathlib 中的一个定理，位于命名空间 `Subsingleton`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst : Preorder α] [inst_1
 : Preorder β] [Subsingleton ι] (f : ι → α)   (g : ι → β) (s : Set ι), MonovaryO
n f g s
参数：f : ι → α；g : ι → β；s : Set ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
protected theorem Subsingleton.monovaryOn [Subsingleton ι] (f : ι → α) (g : ι → β) (s : Set ι) :
    MonovaryOn f g s := fun _ _ _ _ h => (ne_of_apply_ne _ h.ne <| Subsingleton.elim _ _).elim
/-
**Subsingleton.antivaryOn** 是 Mathlib 中的一个定理，位于命名空间 `Subsingleton`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst : Preorder α] [inst_1
 : Preorder β] [Subsingleton ι] (f : ι → α)   (g : ι → β) (s : Set ι), AntivaryO
n f g s
参数：f : ι → α；g : ι → β；s : Set ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
protected theorem Subsingleton.antivaryOn [Subsingleton ι] (f : ι → α) (g : ι → β) (s : Set ι) :
    AntivaryOn f g s := fun _ _ _ _ h => (ne_of_apply_ne _ h.ne <| Subsingleton.elim _ _).elim
/-
**monovaryOn_const_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monovaryOn_const_left (g : ι -> β) (a : α) (s : Set ι) : MonovaryOn (const
 ι a) g s
参数：g : ι -> β；a : α；s : Set ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem monovaryOn_const_left (g : ι → β) (a : α) (s : Set ι) : MonovaryOn (const ι a) g s :=
  fun _ _ _ _ _ => le_rfl
/-
**antivaryOn_const_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antivaryOn_const_left (g : ι -> β) (a : α) (s : Set ι) : AntivaryOn (const
 ι a) g s
参数：g : ι -> β；a : α；s : Set ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem antivaryOn_const_left (g : ι → β) (a : α) (s : Set ι) : AntivaryOn (const ι a) g s :=
  fun _ _ _ _ _ => le_rfl
/-
**monovaryOn_const_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monovaryOn_const_right (f : ι -> α) (b : β) (s : Set ι) : MonovaryOn f (co
nst ι b) s
参数：f : ι -> α；b : β；s : Set ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
theorem monovaryOn_const_right (f : ι → α) (b : β) (s : Set ι) : MonovaryOn f (const ι b) s :=
  fun _ _ _ _ h => (h.ne rfl).elim
/-
**antivaryOn_const_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antivaryOn_const_right (f : ι -> α) (b : β) (s : Set ι) : AntivaryOn f (co
nst ι b) s
参数：f : ι -> α；b : β；s : Set ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
theorem antivaryOn_const_right (f : ι → α) (b : β) (s : Set ι) : AntivaryOn f (const ι b) s :=
  fun _ _ _ _ h => (h.ne rfl).elim
/-
**Monovary.comp_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monovary.comp_right (h : Monovary f g) (k : ι' -> ι) : Monovary (f ∘ k) (g
 ∘ k)
参数：h : Monovary f g；k : ι' -> ι。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Monovary.comp_right (h : Monovary f g) (k : ι' → ι) : Monovary (f ∘ k) (g ∘ k) :=
  fun _ _ hij => h hij
/-
**Antivary.comp_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antivary.comp_right (h : Antivary f g) (k : ι' -> ι) : Antivary (f ∘ k) (g
 ∘ k)
参数：h : Antivary f g；k : ι' -> ι。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Antivary.comp_right (h : Antivary f g) (k : ι' → ι) : Antivary (f ∘ k) (g ∘ k) :=
  fun _ _ hij => h hij
/-
**MonovaryOn.comp_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonovaryOn.comp_right (h : MonovaryOn f g s) (k : ι' -> ι) : MonovaryOn (f
 ∘ k) (g ∘ k) (k ⁻¹' s)
参数：h : MonovaryOn f g s；k : ι' -> ι。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MonovaryOn.comp_right (h : MonovaryOn f g s) (k : ι' → ι) :
    MonovaryOn (f ∘ k) (g ∘ k) (k ⁻¹' s) := fun _ hi _ hj => h hi hj
/-
**AntivaryOn.comp_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntivaryOn.comp_right (h : AntivaryOn f g s) (k : ι' -> ι) : AntivaryOn (f
 ∘ k) (g ∘ k) (k ⁻¹' s)
参数：h : AntivaryOn f g s；k : ι' -> ι。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AntivaryOn.comp_right (h : AntivaryOn f g s) (k : ι' → ι) :
    AntivaryOn (f ∘ k) (g ∘ k) (k ⁻¹' s) := fun _ hi _ hj => h hi hj
/-
**Monovary.comp_monotone_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monovary.comp_monotone_left (h : Monovary f g) (hf : Monotone f') : Monova
ry (f' ∘ f) g
参数：h : Monovary f g；hf : Monotone f'。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Monovary.comp_monotone_left (h : Monovary f g) (hf : Monotone f') : Monovary (f' ∘ f) g :=
  fun _ _ hij => hf <| h hij
/-
**Monovary.comp_antitone_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monovary.comp_antitone_left (h : Monovary f g) (hf : Antitone f') : Antiva
ry (f' ∘ f) g
参数：h : Monovary f g；hf : Antitone f'。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Monovary.comp_antitone_left (h : Monovary f g) (hf : Antitone f') : Antivary (f' ∘ f) g :=
  fun _ _ hij => hf <| h hij
/-
**Antivary.comp_monotone_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antivary.comp_monotone_left (h : Antivary f g) (hf : Monotone f') : Antiva
ry (f' ∘ f) g
参数：h : Antivary f g；hf : Monotone f'。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Antivary.comp_monotone_left (h : Antivary f g) (hf : Monotone f') : Antivary (f' ∘ f) g :=
  fun _ _ hij => hf <| h hij
/-
**Antivary.comp_antitone_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antivary.comp_antitone_left (h : Antivary f g) (hf : Antitone f') : Monova
ry (f' ∘ f) g
参数：h : Antivary f g；hf : Antitone f'。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Antivary.comp_antitone_left (h : Antivary f g) (hf : Antitone f') : Monovary (f' ∘ f) g :=
  fun _ _ hij => hf <| h hij
/-
**MonovaryOn.comp_monotone_on_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonovaryOn.comp_monotone_on_left (h : MonovaryOn f g s) (hf : Monotone f')
 : MonovaryOn (f' ∘ f) g s
参数：h : MonovaryOn f g s；hf : Monotone f'。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MonovaryOn.comp_monotone_on_left (h : MonovaryOn f g s) (hf : Monotone f') :
    MonovaryOn (f' ∘ f) g s := fun _ hi _ hj hij => hf <| h hi hj hij
/-
**MonovaryOn.comp_antitone_on_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonovaryOn.comp_antitone_on_left (h : MonovaryOn f g s) (hf : Antitone f')
 : AntivaryOn (f' ∘ f) g s
参数：h : MonovaryOn f g s；hf : Antitone f'。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MonovaryOn.comp_antitone_on_left (h : MonovaryOn f g s) (hf : Antitone f') :
    AntivaryOn (f' ∘ f) g s := fun _ hi _ hj hij => hf <| h hi hj hij
/-
**AntivaryOn.comp_monotone_on_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntivaryOn.comp_monotone_on_left (h : AntivaryOn f g s) (hf : Monotone f')
 : AntivaryOn (f' ∘ f) g s
参数：h : AntivaryOn f g s；hf : Monotone f'。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AntivaryOn.comp_monotone_on_left (h : AntivaryOn f g s) (hf : Monotone f') :
    AntivaryOn (f' ∘ f) g s := fun _ hi _ hj hij => hf <| h hi hj hij
/-
**AntivaryOn.comp_antitone_on_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntivaryOn.comp_antitone_on_left (h : AntivaryOn f g s) (hf : Antitone f')
 : MonovaryOn (f' ∘ f) g s
参数：h : AntivaryOn f g s；hf : Antitone f'。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AntivaryOn.comp_antitone_on_left (h : AntivaryOn f g s) (hf : Antitone f') :
    MonovaryOn (f' ∘ f) g s := fun _ hi _ hj hij => hf <| h hi hj hij

section OrderDual

open OrderDual

/-
**Monovary.dual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monovary.dual : Monovary f g -> Monovary (toDual ∘ f) (toDual ∘ g)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Monovary.dual : Monovary f g → Monovary (toDual ∘ f) (toDual ∘ g) :=
  swap
/-
**Antivary.dual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antivary.dual : Antivary f g -> Antivary (toDual ∘ f) (toDual ∘ g)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Antivary.dual : Antivary f g → Antivary (toDual ∘ f) (toDual ∘ g) :=
  swap
/-
**Monovary.dual_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monovary.dual_left : Monovary f g -> Antivary (toDual ∘ f) g
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Monovary.dual_left : Monovary f g → Antivary (toDual ∘ f) g :=
  id
/-
**Antivary.dual_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antivary.dual_left : Antivary f g -> Monovary (toDual ∘ f) g
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Antivary.dual_left : Antivary f g → Monovary (toDual ∘ f) g :=
  id
/-
**Monovary.dual_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monovary.dual_right : Monovary f g -> Antivary f (toDual ∘ g)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Monovary.dual_right : Monovary f g → Antivary f (toDual ∘ g) :=
  swap
/-
**Antivary.dual_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antivary.dual_right : Antivary f g -> Monovary f (toDual ∘ g)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Antivary.dual_right : Antivary f g → Monovary f (toDual ∘ g) :=
  swap
/-
**MonovaryOn.dual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonovaryOn.dual : MonovaryOn f g s -> MonovaryOn (toDual ∘ f) (toDual ∘ g)
 s
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MonovaryOn.dual : MonovaryOn f g s → MonovaryOn (toDual ∘ f) (toDual ∘ g) s :=
  swap₂
/-
**AntivaryOn.dual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntivaryOn.dual : AntivaryOn f g s -> AntivaryOn (toDual ∘ f) (toDual ∘ g)
 s
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AntivaryOn.dual : AntivaryOn f g s → AntivaryOn (toDual ∘ f) (toDual ∘ g) s :=
  swap₂
/-
**MonovaryOn.dual_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonovaryOn.dual_left : MonovaryOn f g s -> AntivaryOn (toDual ∘ f) g s
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MonovaryOn.dual_left : MonovaryOn f g s → AntivaryOn (toDual ∘ f) g s :=
  id
/-
**AntivaryOn.dual_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntivaryOn.dual_left : AntivaryOn f g s -> MonovaryOn (toDual ∘ f) g s
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AntivaryOn.dual_left : AntivaryOn f g s → MonovaryOn (toDual ∘ f) g s :=
  id
/-
**MonovaryOn.dual_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonovaryOn.dual_right : MonovaryOn f g s -> AntivaryOn f (toDual ∘ g) s
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MonovaryOn.dual_right : MonovaryOn f g s → AntivaryOn f (toDual ∘ g) s :=
  swap₂
/-
**AntivaryOn.dual_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntivaryOn.dual_right : AntivaryOn f g s -> MonovaryOn f (toDual ∘ g) s
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AntivaryOn.dual_right : AntivaryOn f g s → MonovaryOn f (toDual ∘ g) s :=
  swap₂

@[simp]
/-
**monovary_toDual_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monovary_toDual_left : Monovary (toDual ∘ f) g ↔ Antivary f g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem monovary_toDual_left : Monovary (toDual ∘ f) g ↔ Antivary f g :=
  Iff.rfl

@[simp]
/-
**monovary_toDual_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monovary_toDual_right : Monovary f (toDual ∘ g) ↔ Antivary f g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
theorem monovary_toDual_right : Monovary f (toDual ∘ g) ↔ Antivary f g :=
  forall_comm

@[simp]
/-
**antivary_toDual_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antivary_toDual_left : Antivary (toDual ∘ f) g ↔ Monovary f g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem antivary_toDual_left : Antivary (toDual ∘ f) g ↔ Monovary f g :=
  Iff.rfl

@[simp]
/-
**antivary_toDual_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antivary_toDual_right : Antivary f (toDual ∘ g) ↔ Monovary f g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
theorem antivary_toDual_right : Antivary f (toDual ∘ g) ↔ Monovary f g :=
  forall_comm

@[simp]
/-
**monovaryOn_toDual_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monovaryOn_toDual_left : MonovaryOn (toDual ∘ f) g s ↔ AntivaryOn f g s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem monovaryOn_toDual_left : MonovaryOn (toDual ∘ f) g s ↔ AntivaryOn f g s :=
  Iff.rfl

@[simp]
/-
**monovaryOn_toDual_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monovaryOn_toDual_right : MonovaryOn f (toDual ∘ g) s ↔ AntivaryOn f g s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_comm`：forall₂_comm {ι₁ ι₂ : Sort*} {κ₁ : ι₁ -> Sort*} {κ₂ : ι₂ -
> Sort*} {p : forall i₁, κ₁ i₁ -> forall i₂, κ₂ i₂ -> Prop} : (forall i₁ j₁ i₂ j
₂,…
-/
theorem monovaryOn_toDual_right : MonovaryOn f (toDual ∘ g) s ↔ AntivaryOn f g s :=
  forall₂_comm

@[simp]
/-
**antivaryOn_toDual_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antivaryOn_toDual_left : AntivaryOn (toDual ∘ f) g s ↔ MonovaryOn f g s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem antivaryOn_toDual_left : AntivaryOn (toDual ∘ f) g s ↔ MonovaryOn f g s :=
  Iff.rfl

@[simp]
/-
**antivaryOn_toDual_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antivaryOn_toDual_right : AntivaryOn f (toDual ∘ g) s ↔ MonovaryOn f g s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_comm`：forall₂_comm {ι₁ ι₂ : Sort*} {κ₁ : ι₁ -> Sort*} {κ₂ : ι₂ -
> Sort*} {p : forall i₁, κ₁ i₁ -> forall i₂, κ₂ i₂ -> Prop} : (forall i₁ j₁ i₂ j
₂,…
-/
theorem antivaryOn_toDual_right : AntivaryOn f (toDual ∘ g) s ↔ MonovaryOn f g s :=
  forall₂_comm

end OrderDual

section PartialOrder

variable [PartialOrder ι]

@[simp]
/-
**monovary_id_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monovary_id_iff : Monovary f id ↔ Monotone f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `monotone_iff_forall_lt`：monotone_iff_forall_lt : Monotone f ↔ forall ⦃a 
b⦄, a < b -> f a <= f b
-/
theorem monovary_id_iff : Monovary f id ↔ Monotone f :=
  monotone_iff_forall_lt.symm

@[simp]
/-
**antivary_id_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antivary_id_iff : Antivary f id ↔ Antitone f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `antitone_iff_forall_lt`：antitone_iff_forall_lt : Antitone f ↔ forall ⦃a 
b⦄, a < b -> f b <= f a
-/
theorem antivary_id_iff : Antivary f id ↔ Antitone f :=
  antitone_iff_forall_lt.symm

@[simp]
/-
**monovaryOn_id_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monovaryOn_id_iff : MonovaryOn f id s ↔ MonotoneOn f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `monotoneOn_iff_forall_lt`：monotoneOn_iff_forall_lt : MonotoneOn f s ↔ fo
rall ⦃a⦄ (_ : a in s) ⦃b⦄ (_ : b in s), a < b -> f a <= f b
-/
theorem monovaryOn_id_iff : MonovaryOn f id s ↔ MonotoneOn f s :=
  monotoneOn_iff_forall_lt.symm

@[simp]
/-
**antivaryOn_id_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antivaryOn_id_iff : AntivaryOn f id s ↔ AntitoneOn f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `antitoneOn_iff_forall_lt`：antitoneOn_iff_forall_lt : AntitoneOn f s ↔ fo
rall ⦃a⦄ (_ : a in s) ⦃b⦄ (_ : b in s), a < b -> f b <= f a
-/
theorem antivaryOn_id_iff : AntivaryOn f id s ↔ AntitoneOn f s :=
  antitoneOn_iff_forall_lt.symm
/-
**StrictMono.trans_monovary** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.trans_monovary (hf : StrictMono f) (h : Monovary g f) : Monoton
e g
参数：hf : StrictMono f；h : Monovary g f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `monotone_iff_forall_lt`：monotone_iff_forall_lt : Monotone f ↔ forall ⦃a 
b⦄, a < b -> f a <= f b
-/
lemma StrictMono.trans_monovary (hf : StrictMono f) (h : Monovary g f) : Monotone g :=
  monotone_iff_forall_lt.2 fun _a _b hab ↦ h <| hf hab
/-
**StrictMono.trans_antivary** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.trans_antivary (hf : StrictMono f) (h : Antivary g f) : Antiton
e g
参数：hf : StrictMono f；h : Antivary g f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `antitone_iff_forall_lt`：antitone_iff_forall_lt : Antitone f ↔ forall ⦃a 
b⦄, a < b -> f b <= f a
-/
lemma StrictMono.trans_antivary (hf : StrictMono f) (h : Antivary g f) : Antitone g :=
  antitone_iff_forall_lt.2 fun _a _b hab ↦ h <| hf hab
/-
**StrictAnti.trans_monovary** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAnti.trans_monovary (hf : StrictAnti f) (h : Monovary g f) : Antiton
e g
参数：hf : StrictAnti f；h : Monovary g f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `antitone_iff_forall_lt`：antitone_iff_forall_lt : Antitone f ↔ forall ⦃a 
b⦄, a < b -> f b <= f a
-/
lemma StrictAnti.trans_monovary (hf : StrictAnti f) (h : Monovary g f) : Antitone g :=
  antitone_iff_forall_lt.2 fun _a _b hab ↦ h <| hf hab
/-
**StrictAnti.trans_antivary** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAnti.trans_antivary (hf : StrictAnti f) (h : Antivary g f) : Monoton
e g
参数：hf : StrictAnti f；h : Antivary g f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `monotone_iff_forall_lt`：monotone_iff_forall_lt : Monotone f ↔ forall ⦃a 
b⦄, a < b -> f a <= f b
-/
lemma StrictAnti.trans_antivary (hf : StrictAnti f) (h : Antivary g f) : Monotone g :=
  monotone_iff_forall_lt.2 fun _a _b hab ↦ h <| hf hab
/-
**StrictMonoOn.trans_monovaryOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMonoOn.trans_monovaryOn (hf : StrictMonoOn f s) (h : MonovaryOn g f 
s) : MonotoneOn g s
参数：hf : StrictMonoOn f s；h : MonovaryOn g f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `monotoneOn_iff_forall_lt`：monotoneOn_iff_forall_lt : MonotoneOn f s ↔ fo
rall ⦃a⦄ (_ : a in s) ⦃b⦄ (_ : b in s), a < b -> f a <= f b
-/
lemma StrictMonoOn.trans_monovaryOn (hf : StrictMonoOn f s) (h : MonovaryOn g f s) :
    MonotoneOn g s := monotoneOn_iff_forall_lt.2 fun _a ha _b hb hab ↦ h ha hb <| hf ha hb hab
/-
**StrictMonoOn.trans_antivaryOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMonoOn.trans_antivaryOn (hf : StrictMonoOn f s) (h : AntivaryOn g f 
s) : AntitoneOn g s
参数：hf : StrictMonoOn f s；h : AntivaryOn g f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `antitoneOn_iff_forall_lt`：antitoneOn_iff_forall_lt : AntitoneOn f s ↔ fo
rall ⦃a⦄ (_ : a in s) ⦃b⦄ (_ : b in s), a < b -> f b <= f a
-/
lemma StrictMonoOn.trans_antivaryOn (hf : StrictMonoOn f s) (h : AntivaryOn g f s) :
    AntitoneOn g s := antitoneOn_iff_forall_lt.2 fun _a ha _b hb hab ↦ h ha hb <| hf ha hb hab
/-
**StrictAntiOn.trans_monovaryOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAntiOn.trans_monovaryOn (hf : StrictAntiOn f s) (h : MonovaryOn g f 
s) : AntitoneOn g s
参数：hf : StrictAntiOn f s；h : MonovaryOn g f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `antitoneOn_iff_forall_lt`：antitoneOn_iff_forall_lt : AntitoneOn f s ↔ fo
rall ⦃a⦄ (_ : a in s) ⦃b⦄ (_ : b in s), a < b -> f b <= f a
-/
lemma StrictAntiOn.trans_monovaryOn (hf : StrictAntiOn f s) (h : MonovaryOn g f s) :
    AntitoneOn g s := antitoneOn_iff_forall_lt.2 fun _a ha _b hb hab ↦ h hb ha <| hf ha hb hab
/-
**StrictAntiOn.trans_antivaryOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAntiOn.trans_antivaryOn (hf : StrictAntiOn f s) (h : AntivaryOn g f 
s) : MonotoneOn g s
参数：hf : StrictAntiOn f s；h : AntivaryOn g f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `monotoneOn_iff_forall_lt`：monotoneOn_iff_forall_lt : MonotoneOn f s ↔ fo
rall ⦃a⦄ (_ : a in s) ⦃b⦄ (_ : b in s), a < b -> f a <= f b
-/
lemma StrictAntiOn.trans_antivaryOn (hf : StrictAntiOn f s) (h : AntivaryOn g f s) :
    MonotoneOn g s := monotoneOn_iff_forall_lt.2 fun _a ha _b hb hab ↦ h hb ha <| hf ha hb hab

end PartialOrder

variable [LinearOrder ι]

/-
**Monotone.monovary** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst : Preorder α] [inst_1
 : Preorder β] {f : ι → α} {g : ι → β}   [inst_2 : LinearOrder ι], Monotone f → 
Monotone g → Monovary f g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Monotone.reflect_lt`：Monotone.reflect_lt (hf : Monotone f) {a b : α} (h 
: f a < f b) : a < b
-/
protected theorem Monotone.monovary (hf : Monotone f) (hg : Monotone g) : Monovary f g :=
  fun _ _ hij => hf (hg.reflect_lt hij).le
/-
**Monotone.antivary** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst : Preorder α] [inst_1
 : Preorder β] {f : ι → α} {g : ι → β}   [inst_2 : LinearOrder ι], Monotone f → 
Antitone g → Antivary f g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monovary.dual_right`：Monovary.dual_right : Monovary f g -> Antivary f (t
oDual ∘ g)
· 使用定理 `Monotone.monovary`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst 
: Preorder α] [inst_1 : Preorder β] {f : ι → α} {g : ι → β}   [inst_2 : LinearOr
der ι],…
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)
-/
protected theorem Monotone.antivary (hf : Monotone f) (hg : Antitone g) : Antivary f g :=
  (hf.monovary hg.dual_right).dual_right
/-
**Antitone.monovary** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst : Preorder α] [inst_1
 : Preorder β] {f : ι → α} {g : ι → β}   [inst_2 : LinearOrder ι], Antitone f → 
Antitone g → Monovary f g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antivary.dual_left`：Antivary.dual_left : Antivary f g -> Monovary (toDua
l ∘ f) g
· 使用定理 `Monotone.antivary`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst 
: Preorder α] [inst_1 : Preorder β] {f : ι → α} {g : ι → β}   [inst_2 : LinearOr
der ι],…
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)
-/
protected theorem Antitone.monovary (hf : Antitone f) (hg : Antitone g) : Monovary f g :=
  (hf.dual_right.antivary hg).dual_left
/-
**Antitone.antivary** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst : Preorder α] [inst_1
 : Preorder β] {f : ι → α} {g : ι → β}   [inst_2 : LinearOrder ι], Antitone f → 
Monotone g → Antivary f g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monovary.dual_right`：Monovary.dual_right : Monovary f g -> Antivary f (t
oDual ∘ g)
· 使用定理 `Antitone.monovary`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst 
: Preorder α] [inst_1 : Preorder β] {f : ι → α} {g : ι → β}   [inst_2 : LinearOr
der ι],…
· 使用定理 `Monotone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → Antitone (⇑OrderDual.toDual ∘ f)
-/
protected theorem Antitone.antivary (hf : Antitone f) (hg : Monotone g) : Antivary f g :=
  (hf.monovary hg.dual_right).dual_right
/-
**MonotoneOn.monovaryOn** 是 Mathlib 中的一个定理，位于命名空间 `MonotoneOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst : Preorder α] [inst_1
 : Preorder β] {f : ι → α} {g : ι → β}   {s : Set ι} [inst_2 : LinearOrder ι], M
onotoneOn f s → MonotoneOn g s → MonovaryOn f g s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `MonotoneOn.reflect_lt`：MonotoneOn.reflect_lt (hf : MonotoneOn f s) {a b 
: α} (ha : a in s) (hb : b in s) (h : f a < f b) : a < b
-/
protected theorem MonotoneOn.monovaryOn (hf : MonotoneOn f s) (hg : MonotoneOn g s) :
    MonovaryOn f g s := fun _ hi _ hj hij => hf hi hj (hg.reflect_lt hi hj hij).le
/-
**MonotoneOn.antivaryOn** 是 Mathlib 中的一个定理，位于命名空间 `MonotoneOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst : Preorder α] [inst_1
 : Preorder β] {f : ι → α} {g : ι → β}   {s : Set ι} [inst_2 : LinearOrder ι], M
onotoneOn f s → AntitoneOn g s → AntivaryOn f g s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonovaryOn.dual_right`：MonovaryOn.dual_right : MonovaryOn f g s -> Antiv
aryOn f (toDual ∘ g) s
· 使用定理 `MonotoneOn.monovaryOn`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [i
nst : Preorder α] [inst_1 : Preorder β] {f : ι → α} {g : ι → β}   {s : Set ι} [i
nst_2 : Lin…
· 使用定理 `AntitoneOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (⇑Or
derDual.toD…
-/
protected theorem MonotoneOn.antivaryOn (hf : MonotoneOn f s) (hg : AntitoneOn g s) :
    AntivaryOn f g s :=
  (hf.monovaryOn hg.dual_right).dual_right
/-
**AntitoneOn.monovaryOn** 是 Mathlib 中的一个定理，位于命名空间 `AntitoneOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst : Preorder α] [inst_1
 : Preorder β] {f : ι → α} {g : ι → β}   {s : Set ι} [inst_2 : LinearOrder ι], A
ntitoneOn f s → AntitoneOn g s → MonovaryOn f g s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntivaryOn.dual_left`：AntivaryOn.dual_left : AntivaryOn f g s -> Monovar
yOn (toDual ∘ f) g s
· 使用定理 `MonotoneOn.antivaryOn`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [i
nst : Preorder α] [inst_1 : Preorder β] {f : ι → α} {g : ι → β}   {s : Set ι} [i
nst_2 : Lin…
· 使用定理 `AntitoneOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (⇑Or
derDual.toD…
-/
protected theorem AntitoneOn.monovaryOn (hf : AntitoneOn f s) (hg : AntitoneOn g s) :
    MonovaryOn f g s :=
  (hf.dual_right.antivaryOn hg).dual_left
/-
**AntitoneOn.antivaryOn** 是 Mathlib 中的一个定理，位于命名空间 `AntitoneOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst : Preorder α] [inst_1
 : Preorder β] {f : ι → α} {g : ι → β}   {s : Set ι} [inst_2 : LinearOrder ι], A
ntitoneOn f s → MonotoneOn g s → AntivaryOn f g s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonovaryOn.dual_right`：MonovaryOn.dual_right : MonovaryOn f g s -> Antiv
aryOn f (toDual ∘ g) s
· 使用定理 `AntitoneOn.monovaryOn`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [i
nst : Preorder α] [inst_1 : Preorder β] {f : ι → α} {g : ι → β}   {s : Set ι} [i
nst_2 : Lin…
· 使用定理 `MonotoneOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β} {s : Set α},   MonotoneOn f s → AntitoneOn (⇑Or
derDual.toD…
-/
protected theorem AntitoneOn.antivaryOn (hf : AntitoneOn f s) (hg : MonotoneOn g s) :
    AntivaryOn f g s :=
  (hf.monovaryOn hg.dual_right).dual_right

end Preorder

section LinearOrder

variable [Preorder α] [LinearOrder β] [Preorder γ] {f : ι → α} {g : ι → β} {g' : β → γ}
  {s : Set ι}

/-
**MonovaryOn.comp_monotoneOn_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonovaryOn.comp_monotoneOn_right (h : MonovaryOn f g s) (hg : MonotoneOn g
' (g '' s)) : MonovaryOn f (g' ∘ g) s
参数：h : MonovaryOn f g s；hg : MonotoneOn g' (g '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.reflect_lt`：MonotoneOn.reflect_lt (hf : MonotoneOn f s) {a b 
: α} (ha : a in s) (hb : b in s) (h : f a < f b) : a < b
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem MonovaryOn.comp_monotoneOn_right (h : MonovaryOn f g s) (hg : MonotoneOn g' (g '' s)) :
    MonovaryOn f (g' ∘ g) s := fun _ hi _ hj hij =>
  h hi hj <| hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij
/-
**MonovaryOn.comp_antitoneOn_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonovaryOn.comp_antitoneOn_right (h : MonovaryOn f g s) (hg : AntitoneOn g
' (g '' s)) : AntivaryOn f (g' ∘ g) s
参数：h : MonovaryOn f g s；hg : AntitoneOn g' (g '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntitoneOn.reflect_lt`：AntitoneOn.reflect_lt (hf : AntitoneOn f s) {a b 
: α} (ha : a in s) (hb : b in s) (h : f a < f b) : b < a
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem MonovaryOn.comp_antitoneOn_right (h : MonovaryOn f g s) (hg : AntitoneOn g' (g '' s)) :
    AntivaryOn f (g' ∘ g) s := fun _ hi _ hj hij =>
  h hj hi <| hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij
/-
**AntivaryOn.comp_monotoneOn_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntivaryOn.comp_monotoneOn_right (h : AntivaryOn f g s) (hg : MonotoneOn g
' (g '' s)) : AntivaryOn f (g' ∘ g) s
参数：h : AntivaryOn f g s；hg : MonotoneOn g' (g '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.reflect_lt`：MonotoneOn.reflect_lt (hf : MonotoneOn f s) {a b 
: α} (ha : a in s) (hb : b in s) (h : f a < f b) : a < b
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem AntivaryOn.comp_monotoneOn_right (h : AntivaryOn f g s) (hg : MonotoneOn g' (g '' s)) :
    AntivaryOn f (g' ∘ g) s := fun _ hi _ hj hij =>
  h hi hj <| hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij
/-
**AntivaryOn.comp_antitoneOn_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntivaryOn.comp_antitoneOn_right (h : AntivaryOn f g s) (hg : AntitoneOn g
' (g '' s)) : MonovaryOn f (g' ∘ g) s
参数：h : AntivaryOn f g s；hg : AntitoneOn g' (g '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntitoneOn.reflect_lt`：AntitoneOn.reflect_lt (hf : AntitoneOn f s) {a b 
: α} (ha : a in s) (hb : b in s) (h : f a < f b) : b < a
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem AntivaryOn.comp_antitoneOn_right (h : AntivaryOn f g s) (hg : AntitoneOn g' (g '' s)) :
    MonovaryOn f (g' ∘ g) s := fun _ hi _ hj hij =>
  h hj hi <| hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij

@[symm]
/-
**Monovary.symm** 是 Mathlib 中的一个定理，位于命名空间 `Monovary`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst : Preorder α] [inst_1
 : LinearOrder β] {f : ι → α} {g : ι → β},   Monovary f g → Monovary g f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
protected theorem Monovary.symm (h : Monovary f g) : Monovary g f := fun _ _ hf =>
  le_of_not_gt fun hg => hf.not_ge <| h hg

@[symm]
/-
**Antivary.symm** 是 Mathlib 中的一个定理，位于命名空间 `Antivary`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst : Preorder α] [inst_1
 : LinearOrder β] {f : ι → α} {g : ι → β},   Antivary f g → Antivary g f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
protected theorem Antivary.symm (h : Antivary f g) : Antivary g f := fun _ _ hf =>
  le_of_not_gt fun hg => hf.not_ge <| h hg

@[symm]
/-
**MonovaryOn.symm** 是 Mathlib 中的一个定理，位于命名空间 `MonovaryOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst : Preorder α] [inst_1
 : LinearOrder β] {f : ι → α} {g : ι → β}   {s : Set ι}, MonovaryOn f g s → Mono
varyOn g f s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
protected theorem MonovaryOn.symm (h : MonovaryOn f g s) : MonovaryOn g f s := fun _ hi _ hj hf =>
  le_of_not_gt fun hg => hf.not_ge <| h hj hi hg

@[symm]
/-
**AntivaryOn.symm** 是 Mathlib 中的一个定理，位于命名空间 `AntivaryOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst : Preorder α] [inst_1
 : LinearOrder β] {f : ι → α} {g : ι → β}   {s : Set ι}, AntivaryOn f g s → Anti
varyOn g f s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
protected theorem AntivaryOn.symm (h : AntivaryOn f g s) : AntivaryOn g f s := fun _ hi _ hj hf =>
  le_of_not_gt fun hg => hf.not_ge <| h hi hj hg

end LinearOrder

section LinearOrder

variable [LinearOrder α] [LinearOrder β] {f : ι → α} {g : ι → β} {s : Set ι}

/-
**monovary_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monovary_comm : Monovary f g ↔ Monovary g f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monovary.symm`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst : Pr
eorder α] [inst_1 : LinearOrder β] {f : ι → α} {g : ι → β},   Monovary f g → Mon
ova…
-/
theorem monovary_comm : Monovary f g ↔ Monovary g f :=
  ⟨Monovary.symm, Monovary.symm⟩
/-
**antivary_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antivary_comm : Antivary f g ↔ Antivary g f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antivary.symm`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst : Pr
eorder α] [inst_1 : LinearOrder β] {f : ι → α} {g : ι → β},   Antivary f g → Ant
iva…
-/
theorem antivary_comm : Antivary f g ↔ Antivary g f :=
  ⟨Antivary.symm, Antivary.symm⟩
/-
**monovaryOn_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monovaryOn_comm : MonovaryOn f g s ↔ MonovaryOn g f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonovaryOn.symm`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst : 
Preorder α] [inst_1 : LinearOrder β] {f : ι → α} {g : ι → β}   {s : Set ι}, Mono
varyO…
-/
theorem monovaryOn_comm : MonovaryOn f g s ↔ MonovaryOn g f s :=
  ⟨MonovaryOn.symm, MonovaryOn.symm⟩
/-
**antivaryOn_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antivaryOn_comm : AntivaryOn f g s ↔ AntivaryOn g f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntivaryOn.symm`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst : 
Preorder α] [inst_1 : LinearOrder β] {f : ι → α} {g : ι → β}   {s : Set ι}, Anti
varyO…
-/
theorem antivaryOn_comm : AntivaryOn f g s ↔ AntivaryOn g f s :=
  ⟨AntivaryOn.symm, AntivaryOn.symm⟩

end LinearOrder

