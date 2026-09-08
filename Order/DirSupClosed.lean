/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin, Violeta Hernández Palacios
-/
module

public import Mathlib.Order.Antisymmetrization
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.UpperLower.Basic

import Mathlib.Data.Set.Lattice

/-!
# Sets closed under directed suprema

We say that a set `s` is closed under directed suprema whenever it contains all least upper bounds
for nonempty, directed subsets. Conversely, a set `s` is inaccessible by directed suprema whenever
its complement is closed under directed suprema. Equivalently, if the least upper bound of a
nonempty directed set `t` is contained in `s`, then `t` and `s` must have nonempty intersection.

## Main definitions

- `DirSupClosed`: sets closed under directed suprema.
- `DirSupInacc`: sets inaccessible by directed suprema.
-/

@[expose] public section

variable {α : Type*} {s t : Set α} {D D₁ D₂ : Set (Set α)}

open Set

section Preorder
variable [Preorder α]

/-- A predicate for a set which is closed under directed suprema of nonempty sets.
This is the complement of a `DirSupInaccOn` set. -/
/-
**DirSupClosedOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DirSupClosedOn (D : Set (Set α)) (s : Set α) : Prop
参数：D : Set (Set α)；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate for a set which is closed under directed suprema of nonempty sets.
This is the complement of a `DirSupInaccOn` set.
-/
def DirSupClosedOn (D : Set (Set α)) (s : Set α) : Prop :=
  ∀ ⦃d⦄, d ∈ D → d ⊆ s → d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → a ∈ s

/-- A predicate for a set which is inaccessible by directed suprema of nonempty sets in `D`.
This is the complement of a `DirSupClosedOn` set. -/
/-
**DirSupInaccOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DirSupInaccOn (D : Set (Set α)) (s : Set α) : Prop
参数：D : Set (Set α)；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate for a set which is inaccessible by directed suprema of nonempty sets
 in `D`.
This is the complement of a `DirSupClosedOn` set.
-/
def DirSupInaccOn (D : Set (Set α)) (s : Set α) : Prop :=
  ∀ ⦃d⦄, d ∈ D → d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → a ∈ s → (d ∩ s).Nonempty

/-- A predicate for a set which is closed under directed suprema of nonempty sets.
This is the complement of a `DirSupInacc` set. -/
/-
**DirSupClosed** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DirSupClosed (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate for a set which is closed under directed suprema of nonempty sets.
This is the complement of a `DirSupInacc` set.
-/
def DirSupClosed (s : Set α) : Prop :=
  ∀ ⦃d⦄, d ⊆ s → d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → a ∈ s

/-- A predicate for a set which is inaccessible by directed suprema of nonempty sets.
This is the complement of a `DirSupClosed` set. -/
/-
**DirSupInacc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DirSupInacc (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate for a set which is inaccessible by directed suprema of nonempty sets
.
This is the complement of a `DirSupClosed` set.
-/
def DirSupInacc (s : Set α) : Prop :=
  ∀ ⦃d⦄, d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → a ∈ s → (d ∩ s).Nonempty
/-
**dirSupClosedOn_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {s : Set α} [inst : Preorder α], DirSupClosedOn Set.univ 
s ↔ DirSupClosed s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma dirSupClosedOn_univ : DirSupClosedOn univ s ↔ DirSupClosed s := by
  simp [DirSupClosedOn, DirSupClosed]
/-
**dirSupInaccOn_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {s : Set α} [inst : Preorder α], DirSupInaccOn Set.univ s
 ↔ DirSupInacc s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma dirSupInaccOn_univ : DirSupInaccOn univ s ↔ DirSupInacc s := by
  simp [DirSupInaccOn, DirSupInacc]
/-
**DirSupClosed.dirSupClosedOn** 是 Mathlib 中的一个定理，位于命名空间 `DirSupClosed`。
形式化陈述：∀ {α : Type u_1} {s : Set α} {D : Set (Set α)} [inst : Preorder α], DirSup
Closed s → DirSupClosedOn D s
参数：Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma DirSupClosed.dirSupClosedOn : DirSupClosed s → DirSupClosedOn D s := @fun h _ _ ↦ @h _
/-
**DirSupInacc.dirSupInaccOn** 是 Mathlib 中的一个定理，位于命名空间 `DirSupInacc`。
形式化陈述：∀ {α : Type u_1} {s : Set α} {D : Set (Set α)} [inst : Preorder α], DirSup
Inacc s → DirSupInaccOn D s
参数：Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma DirSupInacc.dirSupInaccOn : DirSupInacc s → DirSupInaccOn D s := @fun h _ _ ↦ @h _
/-
**DirSupClosed.of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `DirSupClosed`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [IsEmpty α] {s : Set α}, DirSupClosed
 s
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem DirSupClosed.of_isEmpty [IsEmpty α] {s : Set α} : DirSupClosed s :=
  fun _ _ ⟨a, _⟩ ↦ isEmptyElim a
/-
**DirSupInacc.of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `DirSupInacc`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [IsEmpty α] {s : Set α}, DirSupInacc 
s
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem DirSupInacc.of_isEmpty [IsEmpty α] {s : Set α} : DirSupInacc s :=
  fun _ ⟨a, _⟩ ↦ isEmptyElim a
/-
**DirSupClosedOn.of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirSupClosedOn.of_isEmpty [IsEmpty α] {s : Set α} : DirSupClosedOn D s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem DirSupClosedOn.of_isEmpty [IsEmpty α] {s : Set α} : DirSupClosedOn D s := by simp
/-
**DirSupInaccOn.of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirSupInaccOn.of_isEmpty [IsEmpty α] {s : Set α} : DirSupInaccOn D s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem DirSupInaccOn.of_isEmpty [IsEmpty α] {s : Set α} : DirSupInaccOn D s := by simp

@[gcongr]
/-
**DirSupClosedOn.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DirSupClosedOn.mono (hD : D₁ subseteq D₂) (hf : DirSupClosedOn D₂ s) : Dir
SupClosedOn D₁ s
参数：hD : D₁ subseteq D₂；hf : DirSupClosedOn D₂ s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma DirSupClosedOn.mono (hD : D₁ ⊆ D₂) (hf : DirSupClosedOn D₂ s) : DirSupClosedOn D₁ s :=
  fun _ a ↦ hf (hD a)

@[gcongr]
/-
**DirSupInaccOn.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DirSupInaccOn.mono (hD : D₁ subseteq D₂) (hf : DirSupInaccOn D₂ s) : DirSu
pInaccOn D₁ s
参数：hD : D₁ subseteq D₂；hf : DirSupInaccOn D₂ s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma DirSupInaccOn.mono (hD : D₁ ⊆ D₂) (hf : DirSupInaccOn D₂ s) : DirSupInaccOn D₁ s :=
  fun _ a ↦ hf (hD a)

@[simp]
/-
**dirSupClosedOn_compl** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dirSupClosedOn_compl : DirSupClosedOn D sᶜ ↔ DirSupInaccOn D s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma dirSupClosedOn_compl : DirSupClosedOn D sᶜ ↔ DirSupInaccOn D s := by
  simp_rw [DirSupClosedOn, DirSupInaccOn, ← not_disjoint_iff_nonempty_inter]
  grind

@[simp]
/-
**dirSupClosed_compl** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dirSupClosed_compl : DirSupClosed sᶜ ↔ DirSupInacc s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dirSupClosedOn_univ`：∀ {α : Type u_1} {s : Set α} [inst : Preorder α], D
irSupClosedOn Set.univ s ↔ DirSupClosed s
· 使用引理 `dirSupClosedOn_compl`：dirSupClosedOn_compl : DirSupClosedOn D sᶜ ↔ DirSu
pInaccOn D s
· 使用定理 `dirSupInaccOn_univ`：∀ {α : Type u_1} {s : Set α} [inst : Preorder α], Di
rSupInaccOn Set.univ s ↔ DirSupInacc s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma dirSupClosed_compl : DirSupClosed sᶜ ↔ DirSupInacc s := by
  rw [← dirSupClosedOn_univ, dirSupClosedOn_compl, dirSupInaccOn_univ]

@[simp]
/-
**dirSupInaccOn_compl** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dirSupInaccOn_compl : DirSupInaccOn D sᶜ ↔ DirSupClosedOn D s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `dirSupClosedOn_compl`：dirSupClosedOn_compl : DirSupClosedOn D sᶜ ↔ DirSu
pInaccOn D s
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma dirSupInaccOn_compl : DirSupInaccOn D sᶜ ↔ DirSupClosedOn D s := by
  rw [← dirSupClosedOn_compl, compl_compl]

@[simp]
/-
**dirSupInacc_compl** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dirSupInacc_compl : DirSupInacc sᶜ ↔ DirSupClosed s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `dirSupClosed_compl`：dirSupClosed_compl : DirSupClosed sᶜ ↔ DirSupInacc s
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma dirSupInacc_compl : DirSupInacc sᶜ ↔ DirSupClosed s := by
  rw [← dirSupClosed_compl, compl_compl]

alias ⟨DirSupInaccOn.of_compl, DirSupInaccOn.compl⟩ := dirSupClosedOn_compl
alias ⟨DirSupClosedOn.of_compl, DirSupClosedOn.compl⟩ := dirSupInaccOn_compl
alias ⟨DirSupInacc.of_compl, DirSupInacc.compl⟩ := dirSupClosed_compl
alias ⟨DirSupClosed.of_compl, DirSupClosed.compl⟩ := dirSupInacc_compl
/-
**DirSupClosed.empty** 是 Mathlib 中的一个定理，位于命名空间 `DirSupClosed`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α], DirSupClosed ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
@[simp] theorem DirSupClosed.empty : DirSupClosed (∅ : Set α) := by simp [DirSupClosed]
/-
**DirSupInacc.empty** 是 Mathlib 中的一个定理，位于命名空间 `DirSupInacc`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α], DirSupInacc ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_empty`：inter_empty (a : Set α) : a inter ∅ = ∅
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] theorem DirSupInacc.empty : DirSupInacc (∅ : Set α) := by simp [DirSupInacc]
/-
**DirSupClosedOn.empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirSupClosedOn.empty : DirSupClosedOn D ∅
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem DirSupClosedOn.empty : DirSupClosedOn D ∅ := by simp
/-
**DirSupInaccOn.empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirSupInaccOn.empty : DirSupInaccOn D ∅
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem DirSupInaccOn.empty : DirSupInaccOn D ∅ := by simp
/-
**DirSupClosed.univ** 是 Mathlib 中的一个定理，位于命名空间 `DirSupClosed`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α], DirSupClosed Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] theorem DirSupClosed.univ : DirSupClosed (univ : Set α) := by simp [DirSupClosed]
/-
**DirSupInacc.univ** 是 Mathlib 中的一个定理，位于命名空间 `DirSupInacc`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α], DirSupInacc Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
@[simp] theorem DirSupInacc.univ : DirSupInacc (univ : Set α) := by simp [← compl_empty]
/-
**DirSupClosedOn.univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirSupClosedOn.univ : DirSupClosedOn D univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem DirSupClosedOn.univ : DirSupClosedOn D univ := by simp
/-
**DirSupInaccOn.univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirSupInaccOn.univ : DirSupInaccOn D univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem DirSupInaccOn.univ : DirSupInaccOn D univ := by simp
/-
**DirSupClosedOn.sInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirSupClosedOn.sInter {s : Set (Set α)} (hs : forall x in s, DirSupClosedO
n D x) : DirSupClosedOn D (⋂₀ s)
参数：Set α；hs : forall x in s, DirSupClosedOn D x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem DirSupClosedOn.sInter {s : Set (Set α)} (hs : ∀ x ∈ s, DirSupClosedOn D x) :
    DirSupClosedOn D (⋂₀ s) :=
  fun _d hD hds hd hd' _a ha t ht ↦ hs t ht hD (hds.trans fun _x hx ↦ hx _ ht) hd hd' ha
/-
**DirSupClosed.sInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirSupClosed.sInter {s : Set (Set α)} (hs : forall x in s, DirSupClosed x)
 : DirSupClosed (⋂₀ s)
参数：Set α；hs : forall x in s, DirSupClosed x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirSupClosedOn.sInter`：DirSupClosedOn.sInter {s : Set (Set α)} (hs : for
all x in s, DirSupClosedOn D x) : DirSupClosedOn D (⋂₀ s)
· 使用定理 `DirSupClosed.dirSupClosedOn`：∀ {α : Type u_1} {s : Set α} {D : Set (Set 
α)} [inst : Preorder α], DirSupClosed s → DirSupClosedOn D s
-/
theorem DirSupClosed.sInter {s : Set (Set α)} (hs : ∀ x ∈ s, DirSupClosed x) :
    DirSupClosed (⋂₀ s) := by
  simpa using DirSupClosedOn.sInter fun x hx ↦ (hs x hx).dirSupClosedOn (D := .univ)
/-
**DirSupInaccOn.sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirSupInaccOn.sUnion {s : Set (Set α)} (hs : forall x in s, DirSupInaccOn 
D x) : DirSupInaccOn D (⋃₀ s)
参数：Set α；hs : forall x in s, DirSupInaccOn D x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `dirSupClosedOn_compl`：dirSupClosedOn_compl : DirSupClosedOn D sᶜ ↔ DirSu
pInaccOn D s
· 使用定理 `Set.compl_sUnion`：compl_sUnion (S : Set (Set α)) : (⋃₀ S)ᶜ = ⋂₀ (compl '
' S)
· 使用定理 `DirSupClosedOn.sInter`：DirSupClosedOn.sInter {s : Set (Set α)} (hs : for
all x in s, DirSupClosedOn D x) : DirSupClosedOn D (⋂₀ s)
· 使用定理 `DirSupInaccOn.compl`：∀ {α : Type u_1} {s : Set α} {D : Set (Set α)} [ins
t : Preorder α], DirSupInaccOn D s → DirSupClosedOn D sᶜ
-/
theorem DirSupInaccOn.sUnion {s : Set (Set α)} (hs : ∀ x ∈ s, DirSupInaccOn D x) :
    DirSupInaccOn D (⋃₀ s) := by
  rw [← dirSupClosedOn_compl, Set.compl_sUnion]
  apply DirSupClosedOn.sInter
  rintro x ⟨x, hx, rfl⟩
  exact (hs x hx).compl
/-
**DirSupInacc.sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirSupInacc.sUnion {s : Set (Set α)} (hs : forall x in s, DirSupInacc x) :
 DirSupInacc (⋃₀ s)
参数：Set α；hs : forall x in s, DirSupInacc x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirSupInaccOn.sUnion`：DirSupInaccOn.sUnion {s : Set (Set α)} (hs : foral
l x in s, DirSupInaccOn D x) : DirSupInaccOn D (⋃₀ s)
· 使用定理 `DirSupInacc.dirSupInaccOn`：∀ {α : Type u_1} {s : Set α} {D : Set (Set α)
} [inst : Preorder α], DirSupInacc s → DirSupInaccOn D s
-/
theorem DirSupInacc.sUnion {s : Set (Set α)} (hs : ∀ x ∈ s, DirSupInacc x) :
    DirSupInacc (⋃₀ s) := by
  simpa using DirSupInaccOn.sUnion fun x hx ↦ (hs x hx).dirSupInaccOn (D := .univ)
/-
**DirSupClosedOn.iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirSupClosedOn.iInter {ι} {f : ι -> Set α} (hs : forall i, DirSupClosedOn 
D (f i)) : DirSupClosedOn D (⋂ i, f i)
参数：hs : forall i, DirSupClosedOn D (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sInter_range`：sInter_range (f : ι -> Set β) : ⋂₀ range f = ⋂ x, f x
· 使用定理 `DirSupClosedOn.sInter`：DirSupClosedOn.sInter {s : Set (Set α)} (hs : for
all x in s, DirSupClosedOn D x) : DirSupClosedOn D (⋂₀ s)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem DirSupClosedOn.iInter {ι} {f : ι → Set α} (hs : ∀ i, DirSupClosedOn D (f i)) :
    DirSupClosedOn D (⋂ i, f i) := by
  rw [← sInter_range f]
  exact DirSupClosedOn.sInter (by simpa)
/-
**DirSupClosed.iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirSupClosed.iInter {ι} {f : ι -> Set α} (hs : forall i, DirSupClosed (f i
)) : DirSupClosed (⋂ i, f i)
参数：hs : forall i, DirSupClosed (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sInter_range`：sInter_range (f : ι -> Set β) : ⋂₀ range f = ⋂ x, f x
· 使用定理 `DirSupClosed.sInter`：DirSupClosed.sInter {s : Set (Set α)} (hs : forall 
x in s, DirSupClosed x) : DirSupClosed (⋂₀ s)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem DirSupClosed.iInter {ι} {f : ι → Set α} (hs : ∀ i, DirSupClosed (f i)) :
    DirSupClosed (⋂ i, f i) := by
  rw [← sInter_range f]
  exact DirSupClosed.sInter (by simpa)
/-
**DirSupInaccOn.iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirSupInaccOn.iUnion {ι} {f : ι -> Set α} (hs : forall i, DirSupInaccOn D 
(f i)) : DirSupInaccOn D (⋃ i, f i)
参数：hs : forall i, DirSupInaccOn D (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sUnion_range`：sUnion_range (f : ι -> Set β) : ⋃₀ range f = ⋃ x, f x
· 使用定理 `DirSupInaccOn.sUnion`：DirSupInaccOn.sUnion {s : Set (Set α)} (hs : foral
l x in s, DirSupInaccOn D x) : DirSupInaccOn D (⋃₀ s)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem DirSupInaccOn.iUnion {ι} {f : ι → Set α} (hs : ∀ i, DirSupInaccOn D (f i)) :
    DirSupInaccOn D (⋃ i, f i) := by
  rw [← sUnion_range f]
  exact DirSupInaccOn.sUnion (by simpa)
/-
**DirSupInacc.iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirSupInacc.iUnion {ι} {f : ι -> Set α} (hs : forall i, DirSupInacc (f i))
 : DirSupInacc (⋃ i, f i)
参数：hs : forall i, DirSupInacc (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sUnion_range`：sUnion_range (f : ι -> Set β) : ⋃₀ range f = ⋃ x, f x
· 使用定理 `DirSupInacc.sUnion`：DirSupInacc.sUnion {s : Set (Set α)} (hs : forall x 
in s, DirSupInacc x) : DirSupInacc (⋃₀ s)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem DirSupInacc.iUnion {ι} {f : ι → Set α} (hs : ∀ i, DirSupInacc (f i)) :
    DirSupInacc (⋃ i, f i) := by
  rw [← sUnion_range f]
  exact DirSupInacc.sUnion (by simpa)
/-
**DirSupClosedOn.inter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DirSupClosedOn.inter (hs : DirSupClosedOn D s) (ht : DirSupClosedOn D t) :
 DirSupClosedOn D (s inter t)
参数：hs : DirSupClosedOn D s；ht : DirSupClosedOn D t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sInter_pair`：sInter_pair (s t : Set α) : ⋂₀ {s, t} = s inter t
· 使用定理 `DirSupClosedOn.sInter`：DirSupClosedOn.sInter {s : Set (Set α)} (hs : for
all x in s, DirSupClosedOn D x) : DirSupClosedOn D (⋂₀ s)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma DirSupClosedOn.inter (hs : DirSupClosedOn D s) (ht : DirSupClosedOn D t) :
    DirSupClosedOn D (s ∩ t) := by
  rw [← sInter_pair]
  refine .sInter ?_
  simpa [hs]
/-
**DirSupClosed.inter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DirSupClosed.inter (hs : DirSupClosed s) (ht : DirSupClosed t) : DirSupClo
sed (s inter t)
参数：hs : DirSupClosed s；ht : DirSupClosed t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DirSupClosedOn.inter`：DirSupClosedOn.inter (hs : DirSupClosedOn D s) (ht
 : DirSupClosedOn D t) : DirSupClosedOn D (s inter t)
· 使用定理 `DirSupClosed.dirSupClosedOn`：∀ {α : Type u_1} {s : Set α} {D : Set (Set 
α)} [inst : Preorder α], DirSupClosed s → DirSupClosedOn D s
-/
lemma DirSupClosed.inter (hs : DirSupClosed s) (ht : DirSupClosed t) : DirSupClosed (s ∩ t) := by
  simpa using hs.dirSupClosedOn.inter ht.dirSupClosedOn (D := .univ)
/-
**DirSupInaccOn.union** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DirSupInaccOn.union (hs : DirSupInaccOn D s) (ht : DirSupInaccOn D t) : Di
rSupInaccOn D (s union t)
参数：hs : DirSupInaccOn D s；ht : DirSupInaccOn D t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `dirSupClosedOn_compl`：dirSupClosedOn_compl : DirSupClosedOn D sᶜ ↔ DirSu
pInaccOn D s
· 使用定理 `Set.compl_union`：compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ
· 使用引理 `DirSupClosedOn.inter`：DirSupClosedOn.inter (hs : DirSupClosedOn D s) (ht
 : DirSupClosedOn D t) : DirSupClosedOn D (s inter t)
· 使用定理 `DirSupInaccOn.compl`：∀ {α : Type u_1} {s : Set α} {D : Set (Set α)} [ins
t : Preorder α], DirSupInaccOn D s → DirSupClosedOn D sᶜ
-/
lemma DirSupInaccOn.union (hs : DirSupInaccOn D s) (ht : DirSupInaccOn D t) :
    DirSupInaccOn D (s ∪ t) := by
  rw [← dirSupClosedOn_compl, compl_union]; exact hs.compl.inter ht.compl
/-
**DirSupInacc.union** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DirSupInacc.union (hs : DirSupInacc s) (ht : DirSupInacc t) : DirSupInacc 
(s union t)
参数：hs : DirSupInacc s；ht : DirSupInacc t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DirSupInaccOn.union`：DirSupInaccOn.union (hs : DirSupInaccOn D s) (ht : 
DirSupInaccOn D t) : DirSupInaccOn D (s union t)
· 使用定理 `DirSupInacc.dirSupInaccOn`：∀ {α : Type u_1} {s : Set α} {D : Set (Set α)
} [inst : Preorder α], DirSupInacc s → DirSupInaccOn D s
-/
lemma DirSupInacc.union (hs : DirSupInacc s) (ht : DirSupInacc t) : DirSupInacc (s ∪ t) := by
  simpa using hs.dirSupInaccOn.union ht.dirSupInaccOn (D := .univ)
/-
**DirSupClosedOn.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirSupClosedOn.union (hDL : IsLowerSet D) (hs : DirSupClosedOn D s) (ht : 
DirSupClosedOn D t) : DirSupClosedOn D (s union t)
参数：hDL : IsLowerSet D；hs : DirSupClosedOn D s；ht : DirSupClosedOn D t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `IsCofinalFor.mono_left`：∀ {α : Type u_1} [inst : Preorder α] {s t u : Se
t α}, s ⊆ t → IsCofinalFor t u → IsCofinalFor s u
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `IsCofinalFor.union_right`：IsCofinalFor.union_right (hc : IsCofinalFor s 
t) : IsCofinalFor (t union s) t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用引理 `IsCofinalFor.nonempty`：IsCofinalFor.nonempty (h : IsCofinalFor s t) (hs 
: s.Nonempty) : t.Nonempty
· 使用定理 `IsLUB.of_isCofinalFor`：IsLUB.of_isCofinalFor {s t : Set α} (hs : IsLUB s
 a) (hts : t subseteq s) (hst : IsCofinalFor s t) : IsLUB t a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `directedOn_union_iff`：directedOn_union_iff : DirectedOn (· <= ·) (s unio
n t) ↔ DirectedOn (· <= ·) s ∧ IsCofinalFor t s ∨ DirectedOn (· <= ·) t ∧ IsCofi
nalFor s t
-/
theorem DirSupClosedOn.union (hDL : IsLowerSet D)
    (hs : DirSupClosedOn D s) (ht : DirSupClosedOn D t) : DirSupClosedOn D (s ∪ t) := by
  intro d hD hdu hd₀ hd₁ a ha
  have hdst : d ∩ s ∪ d ∩ t = d := by grind
  wlog h : DirectedOn (· ≤ ·) (d ∩ s) ∧ IsCofinalFor (d ∩ t) (d ∩ s)
  · rw [union_comm] at hdu hdst ⊢
    exact this hDL ht hs hD hdu hd₀ hd₁ ha hdst <|
      (directedOn_union_iff.mp (by rwa [hdst])).resolve_right h
  obtain ⟨hds, hcof⟩ := h
  have hcof' : IsCofinalFor d (d ∩ s) := hcof.union_right.mono_left hdst.ge
  exact .inl <| hs (hDL inter_subset_left hD) inter_subset_right
    (hcof'.nonempty hd₀) hds (ha.of_isCofinalFor inter_subset_left hcof')
/-
**DirSupInaccOn.inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirSupInaccOn.inter (hDL : IsLowerSet D) (hs : DirSupInaccOn D s) (ht : Di
rSupInaccOn D t) : DirSupInaccOn D (s inter t)
参数：hDL : IsLowerSet D；hs : DirSupInaccOn D s；ht : DirSupInaccOn D t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `dirSupClosedOn_compl`：dirSupClosedOn_compl : DirSupClosedOn D sᶜ ↔ DirSu
pInaccOn D s
· 使用定理 `Set.compl_inter`：compl_inter (s t : Set α) : (s inter t)ᶜ = sᶜ union tᶜ
· 使用定理 `DirSupClosedOn.union`：DirSupClosedOn.union (hDL : IsLowerSet D) (hs : Di
rSupClosedOn D s) (ht : DirSupClosedOn D t) : DirSupClosedOn D (s union t)
· 使用定理 `DirSupInaccOn.compl`：∀ {α : Type u_1} {s : Set α} {D : Set (Set α)} [ins
t : Preorder α], DirSupInaccOn D s → DirSupClosedOn D sᶜ
-/
theorem DirSupInaccOn.inter (hDL : IsLowerSet D)
    (hs : DirSupInaccOn D s) (ht : DirSupInaccOn D t) : DirSupInaccOn D (s ∩ t) := by
  rw [← dirSupClosedOn_compl, compl_inter]; exact hs.compl.union hDL ht.compl
/-
**DirSupClosed.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirSupClosed.union (hs : DirSupClosed s) (ht : DirSupClosed t) : DirSupClo
sed (s union t)
参数：hs : DirSupClosed s；ht : DirSupClosed t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirSupClosedOn.union`：DirSupClosedOn.union (hDL : IsLowerSet D) (hs : Di
rSupClosedOn D s) (ht : DirSupClosedOn D t) : DirSupClosedOn D (s union t)
· 使用定理 `isLowerSet_univ`：∀ {α : Type u_1} [inst : LE α], IsLowerSet Set.univ
· 使用定理 `DirSupClosed.dirSupClosedOn`：∀ {α : Type u_1} {s : Set α} {D : Set (Set 
α)} [inst : Preorder α], DirSupClosed s → DirSupClosedOn D s
-/
theorem DirSupClosed.union (hs : DirSupClosed s) (ht : DirSupClosed t) : DirSupClosed (s ∪ t) := by
  simpa using hs.dirSupClosedOn.union isLowerSet_univ ht.dirSupClosedOn
/-
**DirSupInacc.inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirSupInacc.inter (hs : DirSupInacc s) (ht : DirSupInacc t) : DirSupInacc 
(s inter t)
参数：hs : DirSupInacc s；ht : DirSupInacc t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirSupInaccOn.inter`：DirSupInaccOn.inter (hDL : IsLowerSet D) (hs : DirS
upInaccOn D s) (ht : DirSupInaccOn D t) : DirSupInaccOn D (s inter t)
· 使用定理 `isLowerSet_univ`：∀ {α : Type u_1} [inst : LE α], IsLowerSet Set.univ
· 使用定理 `DirSupInacc.dirSupInaccOn`：∀ {α : Type u_1} {s : Set α} {D : Set (Set α)
} [inst : Preorder α], DirSupInacc s → DirSupInaccOn D s
-/
theorem DirSupInacc.inter (hs : DirSupInacc s) (ht : DirSupInacc t) : DirSupInacc (s ∩ t) := by
  simpa using hs.dirSupInaccOn.inter isLowerSet_univ ht.dirSupInaccOn
/-
**DirSupInaccOn.of_inter_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirSupInaccOn.of_inter_subset (h : forall ⦃d : Set α⦄, d in D -> d.Nonempt
y -> DirectedOn (· <= ·) d -> forall ⦃a : α⦄, IsLUB d a -> a in s -> exists b in
 d, Ici b inter d subseteq s) : DirSupInaccOn D s
参数：h : forall ⦃d : Set α⦄, d in D -> d.Nonempty -> DirectedOn (· <= ·) d -> fora
ll ⦃a : α⦄, IsLUB d a -> a in s -> exists b in d, Ici b inter d subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem DirSupInaccOn.of_inter_subset
    (h : ∀ ⦃d : Set α⦄, d ∈ D → d.Nonempty → DirectedOn (· ≤ ·) d →
      ∀ ⦃a : α⦄, IsLUB d a → a ∈ s → ∃ b ∈ d, Ici b ∩ d ⊆ s) : DirSupInaccOn D s := by
  intro d hd₀ hd₁ hd₂ a hda hd₃
  obtain ⟨b, hbd, hb⟩ := h hd₀ hd₁ hd₂ hda hd₃
  exact ⟨b, hbd, hb ⟨le_rfl, hbd⟩⟩
/-
**DirSupInacc.of_inter_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirSupInacc.of_inter_subset (h : forall ⦃d : Set α⦄, d.Nonempty -> Directe
dOn (· <= ·) d -> forall ⦃a : α⦄, IsLUB d a -> a in s -> exists b in d, Ici b in
ter d subseteq s) : DirSupInacc s
参数：h : forall ⦃d : Set α⦄, d.Nonempty -> DirectedOn (· <= ·) d -> forall ⦃a : α⦄
, IsLUB d a -> a in s -> exists b in d, Ici b inter d subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `dirSupInaccOn_univ`：∀ {α : Type u_1} {s : Set α} [inst : Preorder α], Di
rSupInaccOn Set.univ s ↔ DirSupInacc s
· 使用定理 `DirSupInaccOn.of_inter_subset`：DirSupInaccOn.of_inter_subset (h : forall
 ⦃d : Set α⦄, d in D -> d.Nonempty -> DirectedOn (· <= ·) d -> forall ⦃a : α⦄, I
sLUB d a -> a in s …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem DirSupInacc.of_inter_subset
    (h : ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d →
      ∀ ⦃a : α⦄, IsLUB d a → a ∈ s → ∃ b ∈ d, Ici b ∩ d ⊆ s) : DirSupInacc s :=
  dirSupInaccOn_univ.1 (.of_inter_subset (by simpa))

/-- The condition `(d ∩ s).Nonempty` in `DirSupInaccOn` can be replaced with the stronger
`∃ b ∈ d, Ici b ∩ d ⊆ s` (under mild assumptions on `D`). -/
/-
**dirSupInaccOn_iff_inter_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dirSupInaccOn_iff_inter_subset (hDL : IsLowerSet D) : DirSupInaccOn D s ↔ 
forall ⦃d : Set α⦄, d in D -> d.Nonempty -> DirectedOn (· <= ·) d -> forall ⦃a :
 α⦄, IsLUB d a -> a in s -> exists b in d, Ici b inter d subseteq s where mpr
参数：hDL : IsLowerSet D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用引理 `IsCofinalFor.nonempty`：IsCofinalFor.nonempty (h : IsCofinalFor s t) (hs 
: s.Nonempty) : t.Nonempty
· 使用定理 `DirectedOn.of_isCofinalFor`：DirectedOn.of_isCofinalFor (hd : DirectedOn 
(· <= ·) t) (hst : s subseteq t) (hc : IsCofinalFor t s) : DirectedOn (· <= ·) s
· 使用定理 `IsLUB.of_isCofinalFor`：IsLUB.of_isCofinalFor {s t : Set α} (hs : IsLUB s
 a) (hts : t subseteq s) (hst : IsCofinalFor s t) : IsLUB t a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `DirSupInaccOn.of_inter_subset`：DirSupInaccOn.of_inter_subset (h : forall
 ⦃d : Set α⦄, d in D -> d.Nonempty -> DirectedOn (· <= ·) d -> forall ⦃a : α⦄, I
sLUB d a -> a in s …

--- 原说明 ---
The condition `(d ∩ s).Nonempty` in `DirSupInaccOn` can be replaced with the str
onger
`∃ b ∈ d, Ici b ∩ d ⊆ s` (under mild assumptions on `D`).
-/
theorem dirSupInaccOn_iff_inter_subset (hDL : IsLowerSet D) :
    DirSupInaccOn D s ↔ ∀ ⦃d : Set α⦄, d ∈ D → d.Nonempty → DirectedOn (· ≤ ·) d →
      ∀ ⦃a : α⦄, IsLUB d a → a ∈ s → ∃ b ∈ d, Ici b ∩ d ⊆ s where
  mpr := .of_inter_subset
  mp h t hD ht₀ ht₁ a ha has := by
    by_contra! H
    have hcof : IsCofinalFor t (t \ s) := by grind [IsCofinalFor, not_subset]
    obtain ⟨x, hx, hxs⟩ := h (hDL sdiff_subset hD) (hcof.nonempty ht₀)
      (ht₁.of_isCofinalFor sdiff_subset hcof)
      (ha.of_isCofinalFor sdiff_subset hcof) has
    exact hx.2 hxs

/-- The condition `(d ∩ s).Nonempty` in `DirSupInacc` can be replaced with the stronger
`∃ b ∈ d, Ici b ∩ d ⊆ s`. -/
/-
**dirSupInacc_iff_inter_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dirSupInacc_iff_inter_subset : DirSupInacc s ↔ forall ⦃d : Set α⦄, d.Nonem
pty -> DirectedOn (· <= ·) d -> forall ⦃a : α⦄, IsLUB d a -> a in s -> exists b 
in d, Ici b inter d subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `dirSupInaccOn_iff_inter_subset`：dirSupInaccOn_iff_inter_subset (hDL : Is
LowerSet D) : DirSupInaccOn D s ↔ forall ⦃d : Set α⦄, d in D -> d.Nonempty -> Di
rectedOn (· <= ·) d …
· 使用定理 `isLowerSet_univ`：∀ {α : Type u_1} [inst : LE α], IsLowerSet Set.univ

--- 原说明 ---
The condition `(d ∩ s).Nonempty` in `DirSupInacc` can be replaced with the stron
ger
`∃ b ∈ d, Ici b ∩ d ⊆ s`.
-/
theorem dirSupInacc_iff_inter_subset :
    DirSupInacc s ↔ ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d →
      ∀ ⦃a : α⦄, IsLUB d a → a ∈ s → ∃ b ∈ d, Ici b ∩ d ⊆ s := by
  simpa using dirSupInaccOn_iff_inter_subset isLowerSet_univ
/-
**IsUpperSet.dirSupClosed** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUpperSet.dirSupClosed (hs : IsUpperSet s) : DirSupClosed s
参数：hs : IsUpperSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma IsUpperSet.dirSupClosed (hs : IsUpperSet s) : DirSupClosed s :=
  fun _d hds ⟨_b, hb⟩ _ _a ha ↦ hs (ha.1 hb) <| hds hb
/-
**IsUpperSet.dirSupClosedOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUpperSet.dirSupClosedOn (hs : IsUpperSet s) : DirSupClosedOn D s
参数：hs : IsUpperSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirSupClosed.dirSupClosedOn`：∀ {α : Type u_1} {s : Set α} {D : Set (Set 
α)} [inst : Preorder α], DirSupClosed s → DirSupClosedOn D s
· 使用引理 `IsUpperSet.dirSupClosed`：IsUpperSet.dirSupClosed (hs : IsUpperSet s) : D
irSupClosed s
-/
lemma IsUpperSet.dirSupClosedOn (hs : IsUpperSet s) : DirSupClosedOn D s :=
  hs.dirSupClosed.dirSupClosedOn
/-
**IsLowerSet.dirSupInacc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLowerSet.dirSupInacc (hs : IsLowerSet s) : DirSupInacc s
参数：hs : IsLowerSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirSupInacc.of_compl`：∀ {α : Type u_1} {s : Set α} [inst : Preorder α], 
DirSupClosed sᶜ → DirSupInacc s
· 使用引理 `IsUpperSet.dirSupClosed`：IsUpperSet.dirSupClosed (hs : IsUpperSet s) : D
irSupClosed s
· 使用定理 `IsLowerSet.compl`：∀ {α : Type u_1} [inst : LE α] {s : Set α}, IsLowerSet
 s → IsUpperSet sᶜ
-/
lemma IsLowerSet.dirSupInacc (hs : IsLowerSet s) : DirSupInacc s :=
  .of_compl hs.compl.dirSupClosed
/-
**IsLowerSet.dirSupInaccOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLowerSet.dirSupInaccOn (hs : IsLowerSet s) : DirSupInaccOn D s
参数：hs : IsLowerSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirSupInaccOn.of_compl`：∀ {α : Type u_1} {s : Set α} {D : Set (Set α)} [
inst : Preorder α], DirSupClosedOn D sᶜ → DirSupInaccOn D s
· 使用引理 `IsUpperSet.dirSupClosedOn`：IsUpperSet.dirSupClosedOn (hs : IsUpperSet s)
 : DirSupClosedOn D s
· 使用定理 `IsLowerSet.compl`：∀ {α : Type u_1} [inst : LE α] {s : Set α}, IsLowerSet
 s → IsUpperSet sᶜ
-/
lemma IsLowerSet.dirSupInaccOn (hs : IsLowerSet s) : DirSupInaccOn D s :=
  .of_compl hs.compl.dirSupClosedOn
/-
**DirSupClosed.mem_imp_of_antisymmRel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirSupClosed.mem_imp_of_antisymmRel (hs : DirSupClosed s) {a b : α} (h : A
ntisymmRel (· <= ·) a b) (ha : a in s) : b in s
参数：hs : DirSupClosed s；h : AntisymmRel (· <= ·) a b；ha : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `directedOn_singleton`：directedOn_singleton [Std.Refl r] (a : α) : Direct
edOn r ({a} : Set α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isLUB_congr_of_antisymmRel`：isLUB_congr_of_antisymmRel {a b : α} (h : An
tisymmRel (· <= ·) a b) : IsLUB s a ↔ IsLUB s b
· 使用定理 `isLUB_singleton`：isLUB_singleton : IsLUB {a} a
-/
theorem DirSupClosed.mem_imp_of_antisymmRel (hs : DirSupClosed s) {a b : α}
    (h : AntisymmRel (· ≤ ·) a b) (ha : a ∈ s) : b ∈ s := by
  apply hs (singleton_subset_iff.2 ha) ⟨a, rfl⟩ (directedOn_singleton a)
  rw [← isLUB_congr_of_antisymmRel h]
  exact isLUB_singleton
/-
**DirSupClosed.mem_iff_of_antisymmRel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirSupClosed.mem_iff_of_antisymmRel (hs : DirSupClosed s) {a b : α} (h : A
ntisymmRel (· <= ·) a b) : a in s ↔ b in s
参数：hs : DirSupClosed s；h : AntisymmRel (· <= ·) a b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirSupClosed.mem_imp_of_antisymmRel`：DirSupClosed.mem_imp_of_antisymmRel
 (hs : DirSupClosed s) {a b : α} (h : AntisymmRel (· <= ·) a b) (ha : a in s) : 
b in s
· 使用定理 `AntisymmRel.symm`：AntisymmRel.symm : AntisymmRel r a b -> AntisymmRel r 
b a
-/
theorem DirSupClosed.mem_iff_of_antisymmRel (hs : DirSupClosed s) {a b : α}
    (h : AntisymmRel (· ≤ ·) a b) : a ∈ s ↔ b ∈ s :=
  ⟨hs.mem_imp_of_antisymmRel h, hs.mem_imp_of_antisymmRel h.symm⟩
/-
**DirSupInacc.mem_iff_of_antisymmRel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirSupInacc.mem_iff_of_antisymmRel (hs : DirSupInacc s) {a b : α} (h : Ant
isymmRel (· <= ·) a b) : a in s ↔ b in s
参数：hs : DirSupInacc s；h : AntisymmRel (· <= ·) a b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirSupClosed.mem_iff_of_antisymmRel`：DirSupClosed.mem_iff_of_antisymmRel
 (hs : DirSupClosed s) {a b : α} (h : AntisymmRel (· <= ·) a b) : a in s ↔ b in 
s
· 使用定理 `DirSupInacc.compl`：∀ {α : Type u_1} {s : Set α} [inst : Preorder α], Dir
SupInacc s → DirSupClosed sᶜ
-/
theorem DirSupInacc.mem_iff_of_antisymmRel (hs : DirSupInacc s) {a b : α}
    (h : AntisymmRel (· ≤ ·) a b) : a ∈ s ↔ b ∈ s := by
  simpa [not_iff_not] using hs.compl.mem_iff_of_antisymmRel h
/-
**dirSupClosed_Iic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dirSupClosed_Iic (a : α) : DirSupClosed (Iic a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isLUB_le_iff`：isLUB_le_iff (h : IsLUB s a) : a <= b ↔ b in upperBounds s
-/
lemma dirSupClosed_Iic (a : α) : DirSupClosed (Iic a) :=
  fun _d h _ _ _a ha ↦ (isLUB_le_iff ha).2 h
/-
**dirSupClosedOn_Iic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dirSupClosedOn_Iic (a : α) : DirSupClosedOn D (Iic a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirSupClosed.dirSupClosedOn`：∀ {α : Type u_1} {s : Set α} {D : Set (Set 
α)} [inst : Preorder α], DirSupClosed s → DirSupClosedOn D s
· 使用引理 `dirSupClosed_Iic`：dirSupClosed_Iic (a : α) : DirSupClosed (Iic a)
-/
lemma dirSupClosedOn_Iic (a : α) : DirSupClosedOn D (Iic a) :=
  (dirSupClosed_Iic a).dirSupClosedOn
/-
**dirSupInacc_Iic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dirSupInacc_Iic (a : α) : DirSupInacc (Iic a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLowerSet.dirSupInacc`：IsLowerSet.dirSupInacc (hs : IsLowerSet s) : Dir
SupInacc s
· 使用定理 `isLowerSet_Iic`：∀ {α : Type u_1} [inst : Preorder α] (a : α), IsLowerSet
 (Set.Iic a)
-/
lemma dirSupInacc_Iic (a : α) : DirSupInacc (Iic a) :=
  (isLowerSet_Iic a).dirSupInacc
/-
**dirSupInaccOn_Iic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dirSupInaccOn_Iic (a : α) : DirSupInaccOn D (Iic a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLowerSet.dirSupInaccOn`：IsLowerSet.dirSupInaccOn (hs : IsLowerSet s) :
 DirSupInaccOn D s
· 使用定理 `isLowerSet_Iic`：∀ {α : Type u_1} [inst : Preorder α] (a : α), IsLowerSet
 (Set.Iic a)
-/
lemma dirSupInaccOn_Iic (a : α) : DirSupInaccOn D (Iic a) :=
  (isLowerSet_Iic a).dirSupInaccOn

end Preorder

namespace PartialOrder
variable [PartialOrder α]

/-
**PartialOrder.dirSupClosed_singleton** 是 Mathlib 中的一个定理，位于命名空间 `PartialOrder`。
形式化陈述：dirSupClosed_singleton (a : α) : DirSupClosed {a}
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_singleton_of_eq`：mem_singleton_of_eq {x y : α} (H : x = y) : x i
n ({y} : Set α)
· 使用定理 `IsLUB.unique`：IsLUB.unique (Ha : IsLUB s a) (Hb : IsLUB s b) : a = b
· 使用定理 `isLUB_singleton`：isLUB_singleton : IsLUB {a} a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Nonempty.subset_singleton_iff`：∀ {α : Type u_1} {s : Set α} {a : α},
 s.Nonempty → (s ⊆ {a} ↔ s = {a})
-/
theorem dirSupClosed_singleton (a : α) : DirSupClosed {a} := by
  intro d hda hdn _ b hb
  rw [hdn.subset_singleton_iff] at hda
  subst hda
  exact mem_singleton_of_eq (hb.unique isLUB_singleton)
/-
**PartialOrder.dirSupClosedOn_singleton** 是 Mathlib 中的一个定理，位于命名空间 `PartialOrder`
。
形式化陈述：dirSupClosedOn_singleton (a : α) : DirSupClosedOn D {a}
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirSupClosed.dirSupClosedOn`：∀ {α : Type u_1} {s : Set α} {D : Set (Set 
α)} [inst : Preorder α], DirSupClosed s → DirSupClosedOn D s
· 使用定理 `PartialOrder.dirSupClosed_singleton`：dirSupClosed_singleton (a : α) : Di
rSupClosed {a}
-/
theorem dirSupClosedOn_singleton (a : α) : DirSupClosedOn D {a} :=
  (dirSupClosed_singleton a).dirSupClosedOn

end PartialOrder

section LinearOrder
variable [LinearOrder α]

/-
**dirSupClosedOn_iff_of_linearOrder** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dirSupClosedOn_iff_of_linearOrder : DirSupClosedOn D s ↔ forall ⦃d⦄, d in 
D -> d subseteq s -> d.Nonempty -> forall ⦃a⦄, IsLUB d a -> a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem dirSupClosedOn_iff_of_linearOrder :
    DirSupClosedOn D s ↔ ∀ ⦃d⦄, d ∈ D → d ⊆ s → d.Nonempty → ∀ ⦃a⦄, IsLUB d a → a ∈ s := by
  simp [DirSupClosedOn]
/-
**dirSupClosed_iff_of_linearOrder** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dirSupClosed_iff_of_linearOrder : DirSupClosed s ↔ forall ⦃d⦄, d subseteq 
s -> d.Nonempty -> forall ⦃a⦄, IsLUB d a -> a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem dirSupClosed_iff_of_linearOrder :
    DirSupClosed s ↔ ∀ ⦃d⦄, d ⊆ s → d.Nonempty → ∀ ⦃a⦄, IsLUB d a → a ∈ s := by
  simp [DirSupClosed]
/-
**dirSupInaccOn_iff_of_linearOrder** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dirSupInaccOn_iff_of_linearOrder : DirSupInaccOn D s ↔ forall ⦃d⦄, d in D 
-> d.Nonempty -> forall ⦃a⦄, IsLUB d a -> a in s -> (d inter s).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem dirSupInaccOn_iff_of_linearOrder :
    DirSupInaccOn D s ↔
      ∀ ⦃d⦄, d ∈ D → d.Nonempty → ∀ ⦃a⦄, IsLUB d a → a ∈ s → (d ∩ s).Nonempty := by
  simp [DirSupInaccOn]
/-
**dirSupInacc_iff_of_linearOrder** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dirSupInacc_iff_of_linearOrder : DirSupInacc s ↔ forall ⦃d⦄, d.Nonempty ->
 forall ⦃a⦄, IsLUB d a -> a in s -> (d inter s).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem dirSupInacc_iff_of_linearOrder :
    DirSupInacc s ↔ ∀ ⦃d⦄, d.Nonempty → ∀ ⦃a⦄, IsLUB d a → a ∈ s → (d ∩ s).Nonempty := by
  simp [DirSupInacc]

end LinearOrder

section CompleteLattice
variable [CompleteLattice α]

/-
**dirSupClosedOn_iff_forall_sSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dirSupClosedOn_iff_forall_sSup : DirSupClosedOn D s ↔ forall ⦃d⦄, d in D -
> d subseteq s -> d.Nonempty -> DirectedOn (· <= ·) d -> sSup d in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma dirSupClosedOn_iff_forall_sSup : DirSupClosedOn D s ↔
    ∀ ⦃d⦄, d ∈ D → d ⊆ s → d.Nonempty → DirectedOn (· ≤ ·) d → sSup d ∈ s := by
  simp [DirSupClosedOn, isLUB_iff_sSup_eq]
/-
**dirSupInaccOn_iff_forall_sSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dirSupInaccOn_iff_forall_sSup : DirSupInaccOn D s ↔ forall ⦃d⦄, d in D -> 
d.Nonempty -> DirectedOn (· <= ·) d -> sSup d in s -> (d inter s).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma dirSupInaccOn_iff_forall_sSup : DirSupInaccOn D s ↔
    ∀ ⦃d⦄, d ∈ D → d.Nonempty → DirectedOn (· ≤ ·) d → sSup d ∈ s → (d ∩ s).Nonempty := by
  simp [DirSupInaccOn, isLUB_iff_sSup_eq]
/-
**dirSupClosed_iff_forall_sSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dirSupClosed_iff_forall_sSup : DirSupClosed s ↔ forall ⦃d⦄, d subseteq s -
> d.Nonempty -> DirectedOn (· <= ·) d -> sSup d in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma dirSupClosed_iff_forall_sSup : DirSupClosed s ↔
    ∀ ⦃d⦄, d ⊆ s → d.Nonempty → DirectedOn (· ≤ ·) d → sSup d ∈ s := by
  simp [DirSupClosed, isLUB_iff_sSup_eq]
/-
**dirSupInacc_iff_forall_sSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dirSupInacc_iff_forall_sSup : DirSupInacc s ↔ forall ⦃d⦄, d.Nonempty -> Di
rectedOn (· <= ·) d -> sSup d in s -> (d inter s).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma dirSupInacc_iff_forall_sSup : DirSupInacc s ↔
    ∀ ⦃d⦄, d.Nonempty → DirectedOn (· ≤ ·) d → sSup d ∈ s → (d ∩ s).Nonempty := by
  simp [DirSupInacc, isLUB_iff_sSup_eq]

end CompleteLattice

