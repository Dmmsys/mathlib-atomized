/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.ApplyFun
public import Mathlib.Data.List.GetD
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.List.Basic

/-!
# Turing machine tapes

This file defines the notion of a Turing machine tape, and the operations on it. A tape is a
bidirectional infinite sequence of cells, each of which stores an element of a given alphabet `Γ`.
All but finitely many of the cells are required to hold the blank symbol `default : Γ`.

## Main definitions

* `ListBlank Γ` is the type of one-directional tapes with alphabet `Γ`. Implemented as a quotient
  of `List Γ` by extension by blanks at the end.
* `Tape Γ` is the type of Turing machine tapes with alphabet `Γ`. Implemented as two
  `ListBlank Γ` instances, one for each direction, as well as a head symbol.

-/

@[expose] public section

assert_not_exists MonoidWithZero

open Function (iterate_succ iterate_succ_apply iterate_zero_apply)

namespace Turing

section ListBlank

/-- The `BlankExtends` partial order holds of `l₁` and `l₂` if `l₂` is obtained by adding
blanks (`default : Γ`) to the end of `l₁`. -/
/-
**Turing.BlankExtends** 是 Mathlib 中的一个定义，位于命名空间 `Turing`。
形式化陈述：BlankExtends {Γ} [Inhabited Γ] (l₁ l₂ : List Γ) : Prop
参数：l₁ l₂ : List Γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `BlankExtends` partial order holds of `l₁` and `l₂` if `l₂` is obtained by a
dding
blanks (`default : Γ`) to the end of `l₁`.
-/
def BlankExtends {Γ} [Inhabited Γ] (l₁ l₂ : List Γ) : Prop :=
  ∃ n, l₂ = l₁ ++ List.replicate n default

@[refl]
/-
**Turing.BlankExtends.refl** 是 Mathlib 中的一个定理，位于命名空间 `Turing.BlankExtends`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (l : List Γ), Turing.BlankExtends l 
l
参数：l : List Γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem BlankExtends.refl {Γ} [Inhabited Γ] (l : List Γ) : BlankExtends l l :=
  ⟨0, by simp⟩

@[trans]
/-
**Turing.BlankExtends.trans** 是 Mathlib 中的一个定理，位于命名空间 `Turing.BlankExtends`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] {l₁ l₂ l₃ : List Γ},   Turing.BlankE
xtends l₁ l₂ → Turing.BlankExtends l₂ l₃ → Turing.BlankExtends l₁ l₃
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `List.replicate_append_replicate`：∀ {n : ℕ} {α : Type u_1} {a : α} {m : ℕ
}, List.replicate n a ++ List.replicate m a = List.replicate (n + m) a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem BlankExtends.trans {Γ} [Inhabited Γ] {l₁ l₂ l₃ : List Γ} :
    BlankExtends l₁ l₂ → BlankExtends l₂ l₃ → BlankExtends l₁ l₃ := by
  rintro ⟨i, rfl⟩ ⟨j, rfl⟩
  exact ⟨i + j, by simp⟩
/-
**Turing.BlankExtends.below_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Turing.BlankExtends
`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] {l l₁ l₂ : List Γ},   Turing.BlankEx
tends l l₁ → Turing.BlankExtends l l₂ → l₁.length ≤ l₂.length → Turing.BlankExte
nds l₁ l₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.add_sub_cancel'`：∀ {n m : ℕ}, m ≤ n → m + (n - m) = n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `List.length_replicate`：∀ {α : Type u} {n : ℕ} {a : α}, (List.replicate n
 a).length = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem BlankExtends.below_of_le {Γ} [Inhabited Γ] {l l₁ l₂ : List Γ} :
    BlankExtends l l₁ → BlankExtends l l₂ → l₁.length ≤ l₂.length → BlankExtends l₁ l₂ := by
  rintro ⟨i, rfl⟩ ⟨j, rfl⟩ h; use j - i
  simp only [List.length_append, Nat.add_le_add_iff_left, List.length_replicate] at h
  simp only [← List.replicate_add, Nat.add_sub_cancel' h, List.append_assoc]

/-- Any two extensions by blank `l₁,l₂` of `l` have a common join (which can be taken to be the
longer of `l₁` and `l₂`). -/
/-
**Turing.BlankExtends.above** 是 Mathlib 中的一个定义，位于命名空间 `Turing.BlankExtends`。
形式化陈述：{Γ : Type u_1} →   [inst : Inhabited Γ] →     {l l₁ l₂ : List Γ} →       T
uring.BlankExtends l l₁ →         Turing.BlankExtends l l₂ → { l' // Turing.Blan
kExtends l₁ l' ∧ Turing.BlankExtends l₂ l' }
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any two extensions by blank `l₁,l₂` of `l` have a common join (which can be take
n to be the
longer of `l₁` and `l₂`).
-/
def BlankExtends.above {Γ} [Inhabited Γ] {l l₁ l₂ : List Γ} (h₁ : BlankExtends l l₁)
    (h₂ : BlankExtends l l₂) : { l' // BlankExtends l₁ l' ∧ BlankExtends l₂ l' } :=
  if h : l₁.length ≤ l₂.length then ⟨l₂, h₁.below_of_le h₂ h, BlankExtends.refl _⟩
  else ⟨l₁, BlankExtends.refl _, h₂.below_of_le h₁ (le_of_not_ge h)⟩
/-
**Turing.BlankExtends.above_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Turing.BlankExtends
`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] {l l₁ l₂ : List Γ},   Turing.BlankEx
tends l₁ l → Turing.BlankExtends l₂ l → l₁.length ≤ l₂.length → Turing.BlankExte
nds l₁ l₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.append_cancel_right`：∀ {α : Type u_1} {as bs cs : List α}, as ++ bs
 = cs ++ bs → as = cs
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `List.replicate_add`：replicate_add (m n) (a : α) : replicate (m + n) a = 
replicate m a ++ replicate n a
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Nat.add_le_add_iff_left`：∀ {m k n : ℕ}, n + m ≤ n + k ↔ m ≤ k
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `List.length_replicate`：∀ {α : Type u} {n : ℕ} {a : α}, (List.replicate n
 a).length = n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Nat.add_le_add_iff_right`：∀ {m k n : ℕ}, m + n ≤ k + n ↔ m ≤ k
-/
theorem BlankExtends.above_of_le {Γ} [Inhabited Γ] {l l₁ l₂ : List Γ} :
    BlankExtends l₁ l → BlankExtends l₂ l → l₁.length ≤ l₂.length → BlankExtends l₁ l₂ := by
  rintro ⟨i, rfl⟩ ⟨j, e⟩ h; use i - j
  refine List.append_cancel_right (e.symm.trans ?_)
  rw [List.append_assoc, ← List.replicate_add, Nat.sub_add_cancel]
  apply_fun List.length at e
  simp only [List.length_append, List.length_replicate] at e
  rwa [← Nat.add_le_add_iff_left, e, Nat.add_le_add_iff_right]

/-- `BlankRel` is the symmetric closure of `BlankExtends`, turning it into an equivalence
relation. Two lists are related by `BlankRel` if one extends the other by blanks. -/
/-
**Turing.BlankRel** 是 Mathlib 中的一个定义，位于命名空间 `Turing`。
形式化陈述：BlankRel {Γ} [Inhabited Γ] (l₁ l₂ : List Γ) : Prop
参数：l₁ l₂ : List Γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`BlankRel` is the symmetric closure of `BlankExtends`, turning it into an equiva
lence
relation. Two lists are related by `BlankRel` if one extends the other by blanks
.
-/
def BlankRel {Γ} [Inhabited Γ] (l₁ l₂ : List Γ) : Prop :=
  BlankExtends l₁ l₂ ∨ BlankExtends l₂ l₁

@[refl]
/-
**Turing.BlankRel.refl** 是 Mathlib 中的一个定理，位于命名空间 `Turing.BlankRel`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (l : List Γ), Turing.BlankRel l l
参数：l : List Γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.BlankExtends.refl`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (l : Lis
t Γ), Turing.BlankExtends l l
-/
theorem BlankRel.refl {Γ} [Inhabited Γ] (l : List Γ) : BlankRel l l :=
  Or.inl (BlankExtends.refl _)

@[symm]
/-
**Turing.BlankRel.symm** 是 Mathlib 中的一个定理，位于命名空间 `Turing.BlankRel`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] {l₁ l₂ : List Γ}, Turing.BlankRel l₁
 l₂ → Turing.BlankRel l₂ l₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
-/
theorem BlankRel.symm {Γ} [Inhabited Γ] {l₁ l₂ : List Γ} : BlankRel l₁ l₂ → BlankRel l₂ l₁ :=
  Or.symm

@[trans]
/-
**Turing.BlankRel.trans** 是 Mathlib 中的一个定理，位于命名空间 `Turing.BlankRel`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] {l₁ l₂ l₃ : List Γ},   Turing.BlankR
el l₁ l₂ → Turing.BlankRel l₂ l₃ → Turing.BlankRel l₁ l₃
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem BlankRel.trans {Γ} [Inhabited Γ] {l₁ l₂ l₃ : List Γ} :
    BlankRel l₁ l₂ → BlankRel l₂ l₃ → BlankRel l₁ l₃ := by
  grind [eq_def, BlankExtends.below_of_le, BlankExtends.above_of_le, BlankExtends.trans]

/-- Given two `BlankRel` lists, there exists (constructively) a common join. -/
/-
**Turing.BlankRel.above** 是 Mathlib 中的一个定义，位于命名空间 `Turing.BlankRel`。
形式化陈述：{Γ : Type u_1} →   [inst : Inhabited Γ] →     {l₁ l₂ : List Γ} → Turing.Bl
ankRel l₁ l₂ → { l // Turing.BlankExtends l₁ l ∧ Turing.BlankExtends l₂ l }
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two `BlankRel` lists, there exists (constructively) a common join.
-/
def BlankRel.above {Γ} [Inhabited Γ] {l₁ l₂ : List Γ} (h : BlankRel l₁ l₂) :
    { l // BlankExtends l₁ l ∧ BlankExtends l₂ l } := by
  refine
    if hl : l₁.length ≤ l₂.length then ⟨l₂, Or.elim h id fun h' ↦ ?_, BlankExtends.refl _⟩
    else ⟨l₁, BlankExtends.refl _, Or.elim h (fun h' ↦ ?_) id⟩
  · exact (BlankExtends.refl _).above_of_le h' hl
  · exact (BlankExtends.refl _).above_of_le h' (le_of_not_ge hl)

/-- Given two `BlankRel` lists, there exists (constructively) a common meet. -/
/-
**Turing.BlankRel.below** 是 Mathlib 中的一个定义，位于命名空间 `Turing.BlankRel`。
形式化陈述：{Γ : Type u_1} →   [inst : Inhabited Γ] →     {l₁ l₂ : List Γ} → Turing.Bl
ankRel l₁ l₂ → { l // Turing.BlankExtends l l₁ ∧ Turing.BlankExtends l l₂ }
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two `BlankRel` lists, there exists (constructively) a common meet.
-/
def BlankRel.below {Γ} [Inhabited Γ] {l₁ l₂ : List Γ} (h : BlankRel l₁ l₂) :
    { l // BlankExtends l l₁ ∧ BlankExtends l l₂ } := by
  refine
    if hl : l₁.length ≤ l₂.length then ⟨l₁, BlankExtends.refl _, Or.elim h id fun h' ↦ ?_⟩
    else ⟨l₂, Or.elim h (fun h' ↦ ?_) id, BlankExtends.refl _⟩
  · exact (BlankExtends.refl _).above_of_le h' hl
  · exact (BlankExtends.refl _).above_of_le h' (le_of_not_ge hl)
/-
**Turing.BlankRel.equivalence** 是 Mathlib 中的一个定理，位于命名空间 `Turing.BlankRel`。
形式化陈述：∀ (Γ : Type u_1) [inst : Inhabited Γ], Equivalence Turing.BlankRel
参数：Γ : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.BlankRel.refl`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (l : List Γ)
, Turing.BlankRel l l
· 使用定理 `Turing.BlankRel.symm`：∀ {Γ : Type u_1} [inst : Inhabited Γ] {l₁ l₂ : Lis
t Γ}, Turing.BlankRel l₁ l₂ → Turing.BlankRel l₂ l₁
· 使用定理 `Turing.BlankRel.trans`：∀ {Γ : Type u_1} [inst : Inhabited Γ] {l₁ l₂ l₃ :
 List Γ},   Turing.BlankRel l₁ l₂ → Turing.BlankRel l₂ l₃ → Turing.BlankRel l₁ l
₃
-/
theorem BlankRel.equivalence (Γ) [Inhabited Γ] : Equivalence (@BlankRel Γ _) :=
  ⟨BlankRel.refl, @BlankRel.symm _ _, @BlankRel.trans _ _⟩

/-- Construct a setoid instance for `BlankRel`. -/
@[instance_reducible]
/-
**Turing.BlankRel.setoid** 是 Mathlib 中的一个定义，位于命名空间 `Turing.BlankRel`。
形式化陈述：(Γ : Type u_1) → [Inhabited Γ] → Setoid (List Γ)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.BlankRel.equivalence`：∀ (Γ : Type u_1) [inst : Inhabited Γ], Equi
valence Turing.BlankRel

--- 原说明 ---
Construct a setoid instance for `BlankRel`.
-/
def BlankRel.setoid (Γ) [Inhabited Γ] : Setoid (List Γ) :=
  ⟨_, BlankRel.equivalence _⟩

/-- A `ListBlank Γ` is a quotient of `List Γ` by extension by blanks at the end. This is used to
represent half-tapes of a Turing machine, so that we can pretend that the list continues
infinitely with blanks. -/
/-
**Turing.ListBlank** 是 Mathlib 中的一个定义，位于命名空间 `Turing`。
形式化陈述：ListBlank (Γ) [Inhabited Γ]
参数：Γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `ListBlank Γ` is a quotient of `List Γ` by extension by blanks at the end. Thi
s is used to
represent half-tapes of a Turing machine, so that we can pretend that the list c
ontinues
infinitely with blanks.
-/
def ListBlank (Γ) [Inhabited Γ] :=
  Quotient (BlankRel.setoid Γ)
/-
**Turing.ListBlank.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `Turing.ListBlank`。
形式化陈述：{Γ : Type u_1} → [inst : Inhabited Γ] → Inhabited (Turing.ListBlank Γ)
参数：Turing.ListBlank Γ。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
instance ListBlank.inhabited {Γ} [Inhabited Γ] : Inhabited (ListBlank Γ) :=
  ⟨Quotient.mk'' []⟩
/-
**Turing.ListBlank.hasEmptyc** 是 Mathlib 中的一个定义，位于命名空间 `Turing.ListBlank`。
形式化陈述：{Γ : Type u_1} → [inst : Inhabited Γ] → EmptyCollection (Turing.ListBlank 
Γ)
参数：Turing.ListBlank Γ。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
instance ListBlank.hasEmptyc {Γ} [Inhabited Γ] : EmptyCollection (ListBlank Γ) :=
  ⟨Quotient.mk'' []⟩

/-- A modified version of `Quotient.liftOn'` specialized for `ListBlank`, with the stronger
precondition `BlankExtends` instead of `BlankRel`. -/
/-
**Turing.ListBlank.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `Turing.ListBlank`。
形式化陈述：{Γ : Type u_1} →   [inst : Inhabited Γ] →     {α : Sort u_2} → Turing.List
Blank Γ → (f : List Γ → α) → (∀ (a b : List Γ), Turing.BlankExtends a b → f a = 
f b) → α
参数：f : List Γ → α；∀ (a b : List Γ), Turing.BlankExtends a b → f a = f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A modified version of `Quotient.liftOn'` specialized for `ListBlank`, with the s
tronger
precondition `BlankExtends` instead of `BlankRel`.
-/
protected abbrev ListBlank.liftOn {Γ} [Inhabited Γ] {α} (l : ListBlank Γ) (f : List Γ → α)
    (H : ∀ a b, BlankExtends a b → f a = f b) : α :=
  l.liftOn' f <| by rintro a b (h | h) <;> [exact H _ _ h; exact (H _ _ h).symm]

/-- The quotient map turning a `List` into a `ListBlank`. -/
/-
**Turing.ListBlank.mk** 是 Mathlib 中的一个定义，位于命名空间 `Turing.ListBlank`。
形式化陈述：{Γ : Type u_1} → [inst : Inhabited Γ] → List Γ → Turing.ListBlank Γ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
The quotient map turning a `List` into a `ListBlank`.
-/
def ListBlank.mk {Γ} [Inhabited Γ] : List Γ → ListBlank Γ :=
  Quotient.mk''

@[elab_as_elim]
/-
**Turing.ListBlank.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Turing.ListBlank`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] {p : Turing.ListBlank Γ → Prop} (q :
 Turing.ListBlank Γ),   (∀ (a : List Γ), p (Turing.ListBlank.mk a)) → p q
参数：q : Turing.ListBlank Γ；∀ (a : List Γ), p (Turing.ListBlank.mk a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
-/
protected theorem ListBlank.induction_on {Γ} [Inhabited Γ] {p : ListBlank Γ → Prop}
    (q : ListBlank Γ) (h : ∀ a, p (ListBlank.mk a)) : p q :=
  Quotient.inductionOn' q h

/-- The head of a `ListBlank` is well defined. -/
/-
**Turing.ListBlank.head** 是 Mathlib 中的一个定义，位于命名空间 `Turing.ListBlank`。
形式化陈述：{Γ : Type u_1} → [inst : Inhabited Γ] → Turing.ListBlank Γ → Γ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The head of a `ListBlank` is well defined.
-/
def ListBlank.head {Γ} [Inhabited Γ] (l : ListBlank Γ) : Γ := by
  apply l.liftOn List.headI
  rintro a _ ⟨i, rfl⟩
  cases a
  · cases i <;> rfl
  rfl

@[simp]
/-
**Turing.ListBlank.head_mk** 是 Mathlib 中的一个定理，位于命名空间 `Turing.ListBlank`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (l : List Γ), (Turing.ListBlank.mk l
).head = l.headI
参数：l : List Γ；Turing.ListBlank.mk l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ListBlank.head_mk {Γ} [Inhabited Γ] (l : List Γ) :
    ListBlank.head (ListBlank.mk l) = l.headI :=
  rfl

/-- The tail of a `ListBlank` is well defined (up to the tail of blanks). -/
/-
**Turing.ListBlank.tail** 是 Mathlib 中的一个定义，位于命名空间 `Turing.ListBlank`。
形式化陈述：{Γ : Type u_1} → [inst : Inhabited Γ] → Turing.ListBlank Γ → Turing.ListBl
ank Γ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tail of a `ListBlank` is well defined (up to the tail of blanks).
-/
def ListBlank.tail {Γ} [Inhabited Γ] (l : ListBlank Γ) : ListBlank Γ := by
  apply l.liftOn (fun l ↦ ListBlank.mk l.tail)
  rintro a _ ⟨i, rfl⟩
  refine Quotient.sound' (Or.inl ?_)
  cases a
  · rcases i with - | i <;> [exact ⟨0, rfl⟩; exact ⟨i, rfl⟩]
  exact ⟨i, rfl⟩

@[simp]
/-
**Turing.ListBlank.tail_mk** 是 Mathlib 中的一个定理，位于命名空间 `Turing.ListBlank`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (l : List Γ), (Turing.ListBlank.mk l
).tail = Turing.ListBlank.mk l.tail
参数：l : List Γ；Turing.ListBlank.mk l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ListBlank.tail_mk {Γ} [Inhabited Γ] (l : List Γ) :
    ListBlank.tail (ListBlank.mk l) = ListBlank.mk l.tail :=
  rfl

/-- We can cons an element onto a `ListBlank`. -/
/-
**Turing.ListBlank.cons** 是 Mathlib 中的一个定义，位于命名空间 `Turing.ListBlank`。
形式化陈述：{Γ : Type u_1} → [inst : Inhabited Γ] → Γ → Turing.ListBlank Γ → Turing.Li
stBlank Γ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can cons an element onto a `ListBlank`.
-/
def ListBlank.cons {Γ} [Inhabited Γ] (a : Γ) (l : ListBlank Γ) : ListBlank Γ := by
  apply l.liftOn (fun l ↦ ListBlank.mk (List.cons a l))
  rintro _ _ ⟨i, rfl⟩
  exact Quotient.sound' (Or.inl ⟨i, rfl⟩)

@[simp]
/-
**Turing.ListBlank.cons_mk** 是 Mathlib 中的一个定理，位于命名空间 `Turing.ListBlank`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (a : Γ) (l : List Γ),   Turing.ListB
lank.cons a (Turing.ListBlank.mk l) = Turing.ListBlank.mk (a :: l)
参数：a : Γ；l : List Γ；Turing.ListBlank.mk l；a :: l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ListBlank.cons_mk {Γ} [Inhabited Γ] (a : Γ) (l : List Γ) :
    ListBlank.cons a (ListBlank.mk l) = ListBlank.mk (a :: l) :=
  rfl

@[simp]
/-
**Turing.ListBlank.head_cons** 是 Mathlib 中的一个定理，位于命名空间 `Turing.ListBlank`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (a : Γ) (l : Turing.ListBlank Γ), (T
uring.ListBlank.cons a l).head = a
参数：a : Γ；l : Turing.ListBlank Γ；Turing.ListBlank.cons a l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁ → Prop}
, (∀ (a : α), p (Quotient.mk'' a)) → ∀ (q : Quotient s₁), p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
theorem ListBlank.head_cons {Γ} [Inhabited Γ] (a : Γ) : ∀ l : ListBlank Γ, (l.cons a).head = a :=
  Quotient.ind' fun _ ↦ rfl

@[simp]
/-
**Turing.ListBlank.tail_cons** 是 Mathlib 中的一个定理，位于命名空间 `Turing.ListBlank`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (a : Γ) (l : Turing.ListBlank Γ), (T
uring.ListBlank.cons a l).tail = l
参数：a : Γ；l : Turing.ListBlank Γ；Turing.ListBlank.cons a l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁ → Prop}
, (∀ (a : α), p (Quotient.mk'' a)) → ∀ (q : Quotient s₁), p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
theorem ListBlank.tail_cons {Γ} [Inhabited Γ] (a : Γ) : ∀ l : ListBlank Γ, (l.cons a).tail = l :=
  Quotient.ind' fun _ ↦ rfl

/-- The `cons` and `head`/`tail` functions are mutually inverse, unlike in the case of `List` where
this only holds for nonempty lists. -/
@[simp]
/-
**Turing.ListBlank.cons_head_tail** 是 Mathlib 中的一个定理，位于命名空间 `Turing.ListBlank`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (l : Turing.ListBlank Γ), Turing.Lis
tBlank.cons l.head l.tail = l
参数：l : Turing.ListBlank Γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁ → Prop}
, (∀ (a : α), p (Quotient.mk'' a)) → ∀ (q : Quotient s₁), p q
· 使用定理 `Quotient.sound'`：sound' {a b : α} : s₁ a b -> @Quotient.mk'' α s₁ a = Qu
otient.mk'' b
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Turing.BlankExtends.refl`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (l : Lis
t Γ), Turing.BlankExtends l l

--- 原说明 ---
The `cons` and `head`/`tail` functions are mutually inverse, unlike in the case 
of `List` where
this only holds for nonempty lists.
-/
theorem ListBlank.cons_head_tail {Γ} [Inhabited Γ] : ∀ l : ListBlank Γ, l.tail.cons l.head = l := by
  apply Quotient.ind'
  refine fun l ↦ Quotient.sound' (Or.inr ?_)
  cases l
  · exact ⟨1, rfl⟩
  · rfl

/-- The `cons` and `head`/`tail` functions are mutually inverse, unlike in the case of `List` where
this only holds for nonempty lists. -/
/-
**Turing.ListBlank.exists_cons** 是 Mathlib 中的一个定理，位于命名空间 `Turing.ListBlank`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (l : Turing.ListBlank Γ), ∃ a l', l 
= Turing.ListBlank.cons a l'
参数：l : Turing.ListBlank Γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Turing.ListBlank.cons_head_tail`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (
l : Turing.ListBlank Γ), Turing.ListBlank.cons l.head l.tail = l

--- 原说明 ---
The `cons` and `head`/`tail` functions are mutually inverse, unlike in the case 
of `List` where
this only holds for nonempty lists.
-/
theorem ListBlank.exists_cons {Γ} [Inhabited Γ] (l : ListBlank Γ) :
    ∃ a l', l = ListBlank.cons a l' :=
  ⟨_, _, (ListBlank.cons_head_tail _).symm⟩

/-- The n-th element of a `ListBlank` is well defined for all `n : ℕ`, unlike in a `List`. -/
/-
**Turing.ListBlank.nth** 是 Mathlib 中的一个定义，位于命名空间 `Turing.ListBlank`。
形式化陈述：{Γ : Type u_1} → [inst : Inhabited Γ] → Turing.ListBlank Γ → ℕ → Γ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The n-th element of a `ListBlank` is well defined for all `n : ℕ`, unlike in a `
List`.
-/
def ListBlank.nth {Γ} [Inhabited Γ] (l : ListBlank Γ) (n : ℕ) : Γ := by
  apply l.liftOn (fun l ↦ List.getI l n)
  rintro l _ ⟨i, rfl⟩
  rcases lt_or_ge n _ with h | h
  · rw [List.getI_append _ _ _ h]
  rw [List.getI_eq_default _ h]
  rcases le_or_gt _ n with h₂ | h₂
  · rw [List.getI_eq_default _ h₂]
  rw [List.getI_eq_getElem _ h₂, List.getElem_append_right h, List.getElem_replicate]

@[simp]
/-
**Turing.ListBlank.nth_mk** 是 Mathlib 中的一个定理，位于命名空间 `Turing.ListBlank`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (l : List Γ) (n : ℕ), (Turing.ListBl
ank.mk l).nth n = l.getI n
参数：l : List Γ；n : ℕ；Turing.ListBlank.mk l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ListBlank.nth_mk {Γ} [Inhabited Γ] (l : List Γ) (n : ℕ) :
    (ListBlank.mk l).nth n = l.getI n :=
  rfl

@[simp]
/-
**Turing.ListBlank.nth_zero** 是 Mathlib 中的一个定理，位于命名空间 `Turing.ListBlank`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (l : Turing.ListBlank Γ), l.nth 0 = 
l.head
参数：l : Turing.ListBlank Γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Turing.ListBlank.cons_head_tail`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (
l : Turing.ListBlank Γ), Turing.ListBlank.cons l.head l.tail = l
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
theorem ListBlank.nth_zero {Γ} [Inhabited Γ] (l : ListBlank Γ) : l.nth 0 = l.head := by
  rw [← ListBlank.cons_head_tail l]
  induction l.tail using Quotient.inductionOn'
  rfl

@[simp]
/-
**Turing.ListBlank.nth_succ** 是 Mathlib 中的一个定理，位于命名空间 `Turing.ListBlank`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (l : Turing.ListBlank Γ) (n : ℕ), l.
nth (n + 1) = l.tail.nth n
参数：l : Turing.ListBlank Γ；n : ℕ；n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Turing.ListBlank.cons_head_tail`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (
l : Turing.ListBlank Γ), Turing.ListBlank.cons l.head l.tail = l
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
theorem ListBlank.nth_succ {Γ} [Inhabited Γ] (l : ListBlank Γ) (n : ℕ) :
    l.nth (n + 1) = l.tail.nth n := by
  rw [← ListBlank.cons_head_tail l]
  induction l.tail using Quotient.inductionOn'
  rfl

@[ext]
/-
**Turing.ListBlank.ext** 是 Mathlib 中的一个定理，位于命名空间 `Turing.ListBlank`。
形式化陈述：∀ {Γ : Type u_1} [i : Inhabited Γ] {L₁ L₂ : Turing.ListBlank Γ}, (∀ (i_1 :
 ℕ), L₁.nth i_1 = L₂.nth i_1) → L₁ = L₂
参数：∀ (i_1 : ℕ), L₁.nth i_1 = L₂.nth i_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.ListBlank.induction_on`：∀ {Γ : Type u_1} [inst : Inhabited Γ] {p 
: Turing.ListBlank Γ → Prop} (q : Turing.ListBlank Γ),   (∀ (a : List Γ), p (Tur
ing.ListBlank.mk a)…
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Quotient.sound'`：sound' {a b : α} : s₁ a b -> @Quotient.mk'' α s₁ a = Qu
otient.mk'' b
· 使用定理 `List.ext_getElem`：ext_getElem?' {l₁ l₂ : List α} (h' : forall n < max l₁
.length l₂.length, l₁[n]? = l₂[n]?) : l₁ = l₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `List.length_replicate`：∀ {α : Type u} {n : ℕ} {a : α}, (List.replicate n
 a).length = n
· 使用定理 `Nat.add_sub_cancel'`：∀ {n m : ℕ}, m ≤ n → m + (n - m) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.getElem_append`：∀ {α : Type u_1} {l₁ l₂ : List α} {i : ℕ} (h : i < 
(l₁ ++ l₂).length),   (l₁ ++ l₂)[i] = if h' : i < l₁.length then l₁[i] else l₂[i
 - l₁.len…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `List.getI_eq_getElem`：getI_eq_getElem {n : Nat} (hn : n < l.length) : l.
getI n = l[n]
· 使用定理 `List.getElem_append_right`：∀ {α : Type u_1} {as bs : List α} {i : ℕ} (h₁
 : as.length ≤ i) {h₂ : i < (as ++ bs).length},   (as ++ bs)[i] = bs[i - as.leng
th]
· 使用定理 `List.getElem_replicate`：∀ {α : Type u_1} {a : α} {n i : ℕ} (h : i < (Lis
t.replicate n a).length), (List.replicate n a)[i] = a
· 使用定理 `List.getI_eq_default`：getI_eq_default {n : Nat} (hn : l.length <= n) : l
.getI n = default
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
-/
theorem ListBlank.ext {Γ} [i : Inhabited Γ] {L₁ L₂ : ListBlank Γ} :
    (∀ i, L₁.nth i = L₂.nth i) → L₁ = L₂ := by
  refine ListBlank.induction_on L₁ fun l₁ ↦ ListBlank.induction_on L₂ fun l₂ H ↦ ?_
  wlog h : l₁.length ≤ l₂.length
  · cases le_total l₁.length l₂.length <;> [skip; symm] <;> apply this <;> try assumption
    intro
    rw [H]
  refine Quotient.sound' (Or.inl ⟨l₂.length - l₁.length, ?_⟩)
  refine List.ext_getElem ?_ fun i h h₂ ↦ Eq.symm ?_
  · simp only [Nat.add_sub_cancel' h, List.length_append, List.length_replicate]
  simp only [ListBlank.nth_mk] at H
  rcases lt_or_ge i l₁.length with h' | h'
  · simp [h', List.getElem_append h₂, ← List.getI_eq_getElem _ h, ← List.getI_eq_getElem _ h', H]
  · rw [List.getElem_append_right h', List.getElem_replicate,
      ← List.getI_eq_default _ h', H, List.getI_eq_getElem _ h]

/-- Apply a function to a value stored at the nth position of the list. -/
@[simp]
/-
**Turing.ListBlank.modifyNth** 是 Mathlib 中的一个定义，位于命名空间 `Turing.ListBlank`。
形式化陈述：{Γ : Type u_1} → [inst : Inhabited Γ] → (Γ → Γ) → ℕ → Turing.ListBlank Γ →
 Turing.ListBlank Γ
参数：Γ → Γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Apply a function to a value stored at the nth position of the list.
-/
def ListBlank.modifyNth {Γ} [Inhabited Γ] (f : Γ → Γ) : ℕ → ListBlank Γ → ListBlank Γ
  | 0, L => L.tail.cons (f L.head)
  | n + 1, L => (L.tail.modifyNth f n).cons L.head
/-
**Turing.ListBlank.nth_modifyNth** 是 Mathlib 中的一个定理，位于命名空间 `Turing.ListBlank`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (f : Γ → Γ) (n i : ℕ) (L : Turing.Li
stBlank Γ),   (Turing.ListBlank.modifyNth f n L).nth i = if i = n then f (L.nth 
i) else L.nth i
参数：f : Γ → Γ；n i : ℕ；L : Turing.ListBlank Γ；Turing.ListBlank.modifyNth f n L；L.n
th i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Turing.ListBlank.nth_zero`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (l : Tu
ring.ListBlank Γ), l.nth 0 = l.head
· 使用定理 `Turing.ListBlank.head_cons`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (a : Γ
) (l : Turing.ListBlank Γ), (Turing.ListBlank.cons a l).head = a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Turing.ListBlank.nth_succ`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (l : Tu
ring.ListBlank Γ) (n : ℕ), l.nth (n + 1) = l.tail.nth n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Turing.ListBlank.tail_cons`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (a : Γ
) (l : Turing.ListBlank Γ), (Turing.ListBlank.cons a l).tail = l
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `Nat.succ.injEq`：∀ (u v : ℕ), (u.succ = v.succ) = (u = v)
-/
theorem ListBlank.nth_modifyNth {Γ} [Inhabited Γ] (f : Γ → Γ) (n i) (L : ListBlank Γ) :
    (L.modifyNth f n).nth i = if i = n then f (L.nth i) else L.nth i := by
  induction n generalizing i L with
  | zero =>
    cases i <;> simp only [ListBlank.nth_zero, if_true, ListBlank.head_cons, ListBlank.modifyNth,
      ListBlank.nth_succ, if_false, ListBlank.tail_cons, reduceCtorEq]
  | succ n IH =>
    cases i
    · rw [if_neg (Nat.succ_ne_zero _).symm]
      simp only [ListBlank.nth_zero, ListBlank.head_cons, ListBlank.modifyNth]
    · simp only [IH, ListBlank.modifyNth, ListBlank.nth_succ, ListBlank.tail_cons, Nat.succ.injEq]

/-- A pointed map of `Inhabited` types is a map that sends one default value to the other. -/
/-
**Turing.PointedMap.** 是 Mathlib 中的一个结构，位于命名空间 `Turing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pointed map of `Inhabited` types is a map that sends one default value to the 
other.
-/
structure PointedMap.{u, v} (Γ : Type u) (Γ' : Type v) [Inhabited Γ] [Inhabited Γ'] :
    Type max u v where
  /-- The map underlying this instance. -/
  f : Γ → Γ'
  map_pt' : f default = default
/-
**Turing.** 是 Mathlib 中的一个实例，位于命名空间 `Turing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] : Inhabited (PointedMap Γ Γ') :=
  ⟨⟨default, rfl⟩⟩
/-
**Turing.** 是 Mathlib 中的一个实例，位于命名空间 `Turing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] : CoeFun (PointedMap Γ Γ') fun _ ↦ Γ → Γ' :=
  ⟨PointedMap.f⟩
/-
**Turing.PointedMap.mk_val** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PointedMap`。
形式化陈述：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inhabited Γ] [inst_1 : Inhabited 
Γ'] (f : Γ → Γ') (pt : f default = default),   { f := f, map_pt' := pt }.f = f
参数：f : Γ → Γ'；pt : f default = default。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PointedMap.mk_val {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : Γ → Γ') (pt) :
    (PointedMap.mk f pt : Γ → Γ') = f :=
  rfl

@[simp]
/-
**Turing.PointedMap.map_pt** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PointedMap`。
形式化陈述：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inhabited Γ] [inst_1 : Inhabited 
Γ'] (f : Turing.PointedMap Γ Γ'),   f.f default = default
参数：f : Turing.PointedMap Γ Γ'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PointedMap.map_pt'`：∀ {Γ : Type u} {Γ' : Type v} [inst : Inhabite
d Γ] [inst_1 : Inhabited Γ'] (self : Turing.PointedMap Γ Γ'),   self.f default =
 default
-/
theorem PointedMap.map_pt {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') :
    f default = default :=
  PointedMap.map_pt' _

@[simp]
/-
**Turing.PointedMap.headI_map** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PointedMap`。
形式化陈述：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inhabited Γ] [inst_1 : Inhabited 
Γ'] (f : Turing.PointedMap Γ Γ') (l : List Γ),   (List.map f.f l).headI = f.f l.
headI
参数：f : Turing.PointedMap Γ Γ'；l : List Γ；List.map f.f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Turing.PointedMap.map_pt`：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inhab
ited Γ] [inst_1 : Inhabited Γ'] (f : Turing.PointedMap Γ Γ'),   f.f default = de
fault
-/
theorem PointedMap.headI_map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
    (l : List Γ) : (l.map f).headI = f l.headI := by
  cases l <;> [exact (PointedMap.map_pt f).symm; rfl]

/-- The `map` function on lists is well defined on `ListBlank`s provided that the map is
pointed. -/
/-
**Turing.ListBlank.map** 是 Mathlib 中的一个定义，位于命名空间 `Turing.ListBlank`。
形式化陈述：{Γ : Type u_1} →   {Γ' : Type u_2} →     [inst : Inhabited Γ] → [inst_1 : 
Inhabited Γ'] → Turing.PointedMap Γ Γ' → Turing.ListBlank Γ → Turing.ListBlank Γ
'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `map` function on lists is well defined on `ListBlank`s provided that the ma
p is
pointed.
-/
def ListBlank.map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (l : ListBlank Γ) :
    ListBlank Γ' := by
  apply l.liftOn (fun l ↦ ListBlank.mk (List.map f l))
  rintro l _ ⟨i, rfl⟩; refine Quotient.sound' (Or.inl ⟨i, ?_⟩)
  simp only [PointedMap.map_pt, List.map_append, List.map_replicate]

@[simp]
/-
**Turing.ListBlank.map_mk** 是 Mathlib 中的一个定理，位于命名空间 `Turing.ListBlank`。
形式化陈述：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inhabited Γ] [inst_1 : Inhabited 
Γ'] (f : Turing.PointedMap Γ Γ') (l : List Γ),   Turing.ListBlank.map f (Turing.
ListBlank.mk l) = Turing.ListBlank.mk (List.map f.f l)
参数：f : Turing.PointedMap Γ Γ'；l : List Γ；Turing.ListBlank.mk l；List.map f.f l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ListBlank.map_mk {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (l : List Γ) :
    (ListBlank.mk l).map f = ListBlank.mk (l.map f) :=
  rfl

@[simp]
/-
**Turing.ListBlank.head_map** 是 Mathlib 中的一个定理，位于命名空间 `Turing.ListBlank`。
形式化陈述：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inhabited Γ] [inst_1 : Inhabited 
Γ'] (f : Turing.PointedMap Γ Γ')   (l : Turing.ListBlank Γ), (Turing.ListBlank.m
ap f l).head = f.f l.head
参数：f : Turing.PointedMap Γ Γ'；l : Turing.ListBlank Γ；Turing.ListBlank.map f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Turing.ListBlank.cons_head_tail`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (
l : Turing.ListBlank Γ), Turing.ListBlank.cons l.head l.tail = l
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
theorem ListBlank.head_map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
    (l : ListBlank Γ) : (l.map f).head = f l.head := by
  rw [← ListBlank.cons_head_tail l]
  induction l using Quotient.inductionOn'
  rfl

@[simp]
/-
**Turing.ListBlank.tail_map** 是 Mathlib 中的一个定理，位于命名空间 `Turing.ListBlank`。
形式化陈述：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inhabited Γ] [inst_1 : Inhabited 
Γ'] (f : Turing.PointedMap Γ Γ')   (l : Turing.ListBlank Γ), (Turing.ListBlank.m
ap f l).tail = Turing.ListBlank.map f l.tail
参数：f : Turing.PointedMap Γ Γ'；l : Turing.ListBlank Γ；Turing.ListBlank.map f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Turing.ListBlank.cons_head_tail`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (
l : Turing.ListBlank Γ), Turing.ListBlank.cons l.head l.tail = l
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
theorem ListBlank.tail_map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
    (l : ListBlank Γ) : (l.map f).tail = l.tail.map f := by
  rw [← ListBlank.cons_head_tail l]
  induction l using Quotient.inductionOn'
  rfl

@[simp]
/-
**Turing.ListBlank.map_cons** 是 Mathlib 中的一个定理，位于命名空间 `Turing.ListBlank`。
形式化陈述：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inhabited Γ] [inst_1 : Inhabited 
Γ'] (f : Turing.PointedMap Γ Γ')   (l : Turing.ListBlank Γ) (a : Γ),   Turing.Li
stBlank.map f (Turing.ListBlank.cons a l) = Turing.ListBlank.cons (f.f a) (Turin
g.ListBlank.map f l)
参数：f : Turing.PointedMap Γ Γ'；l : Turing.ListBlank Γ；a : Γ；Turing.ListBlank.cons
 a l；f.f a；Turing.ListBlank.map f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Turing.ListBlank.cons_head_tail`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (
l : Turing.ListBlank Γ), Turing.ListBlank.cons l.head l.tail = l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Turing.ListBlank.head_map`：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inha
bited Γ] [inst_1 : Inhabited Γ'] (f : Turing.PointedMap Γ Γ')   (l : Turing.List
Blank Γ), (Turi…
· 使用定理 `Turing.ListBlank.head_cons`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (a : Γ
) (l : Turing.ListBlank Γ), (Turing.ListBlank.cons a l).head = a
· 使用定理 `Turing.ListBlank.tail_map`：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inha
bited Γ] [inst_1 : Inhabited Γ'] (f : Turing.PointedMap Γ Γ')   (l : Turing.List
Blank Γ), (Turi…
· 使用定理 `Turing.ListBlank.tail_cons`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (a : Γ
) (l : Turing.ListBlank Γ), (Turing.ListBlank.cons a l).tail = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ListBlank.map_cons {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
    (l : ListBlank Γ) (a : Γ) : (l.cons a).map f = (l.map f).cons (f a) := by
  refine (ListBlank.cons_head_tail _).symm.trans ?_
  simp only [ListBlank.head_map, ListBlank.head_cons, ListBlank.tail_map, ListBlank.tail_cons]

@[simp]
/-
**Turing.ListBlank.nth_map** 是 Mathlib 中的一个定理，位于命名空间 `Turing.ListBlank`。
形式化陈述：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inhabited Γ] [inst_1 : Inhabited 
Γ'] (f : Turing.PointedMap Γ Γ')   (l : Turing.ListBlank Γ) (n : ℕ), (Turing.Lis
tBlank.map f l).nth n = f.f (l.nth n)
参数：f : Turing.PointedMap Γ Γ'；l : Turing.ListBlank Γ；n : ℕ；Turing.ListBlank.map 
f l；l.nth n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.ListBlank.induction_on`：∀ {Γ : Type u_1} [inst : Inhabited Γ] {p 
: Turing.ListBlank Γ → Prop} (q : Turing.ListBlank Γ),   (∀ (a : List Γ), p (Tur
ing.ListBlank.mk a)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.getD_map`：getD_map {n : Nat} (f : α -> β) : (map f l).getD n (f d) 
= f (l.getD n d)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.getD_eq_getElem?_getD`：∀ {α : Type u_1} {l : List α} {i : ℕ} {a : α
}, l.getD i a = l[i]?.getD a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.getElem?_map`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List
 α} {i : ℕ}, (List.map f l)[i]? = Option.map f l[i]?
· 使用定理 `Turing.PointedMap.map_pt`：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inhab
ited Γ] [inst_1 : Inhabited Γ'] (f : Turing.PointedMap Γ Γ'),   f.f default = de
fault
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ListBlank.nth_map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
    (l : ListBlank Γ) (n : ℕ) : (l.map f).nth n = f (l.nth n) := by
  refine l.induction_on fun l ↦ ?_
  simp only [ListBlank.map_mk, ListBlank.nth_mk, ← List.getD_default_eq_getI]
  rw [← List.getD_map _ _ f]
  simp

/-- The `i`-th projection as a pointed map. -/
/-
**Turing.proj** 是 Mathlib 中的一个定义，位于命名空间 `Turing`。
形式化陈述：proj {ι : Type*} {Γ : ι -> Type*} [forall i, Inhabited (Γ i)] (i : ι) : Po
intedMap (forall i, Γ i) (Γ i)
参数：Γ i；i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `i`-th projection as a pointed map.
-/
def proj {ι : Type*} {Γ : ι → Type*} [∀ i, Inhabited (Γ i)] (i : ι) :
    PointedMap (∀ i, Γ i) (Γ i) :=
  ⟨fun a ↦ a i, rfl⟩
/-
**Turing.proj_map_nth** 是 Mathlib 中的一个定理，位于命名空间 `Turing`。
形式化陈述：proj_map_nth {ι : Type*} {Γ : ι -> Type*} [forall i, Inhabited (Γ i)] (i :
 ι) (L n) : (ListBlank.map (@proj ι Γ _ i) L).nth n = L.nth n i
参数：Γ i；i : ι；L n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Turing.ListBlank.nth_map`：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inhab
ited Γ] [inst_1 : Inhabited Γ'] (f : Turing.PointedMap Γ Γ')   (l : Turing.ListB
lank Γ) (n : ℕ…
-/
theorem proj_map_nth {ι : Type*} {Γ : ι → Type*} [∀ i, Inhabited (Γ i)] (i : ι) (L n) :
    (ListBlank.map (@proj ι Γ _ i) L).nth n = L.nth n i := by
  rw [ListBlank.nth_map]; rfl
/-
**Turing.ListBlank.map_modifyNth** 是 Mathlib 中的一个定理，位于命名空间 `Turing.ListBlank`。
形式化陈述：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inhabited Γ] [inst_1 : Inhabited 
Γ'] (F : Turing.PointedMap Γ Γ') (f : Γ → Γ)   (f' : Γ' → Γ'),   (∀ (x : Γ), F.f
 (f x) = f' (F.f x)) →     ∀ (n : ℕ) (L : Turing.ListBlank Γ),       Turing.List
Blank.map F (Turing.ListBlank.modifyNth f n L) =         Turing.ListBlank.modify
Nth f' n (Turing.ListBlank.map F L)
参数：F : Turing.PointedMap Γ Γ'；f : Γ → Γ；f' : Γ' → Γ'；∀ (x : Γ), F.f (f x) = f' (
F.f x)；n : ℕ；L : Turing.ListBlank Γ；Turing.ListBlank.modifyNth f n L；Turing.List
Blank.map F L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Turing.ListBlank.map_cons`：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inha
bited Γ] [inst_1 : Inhabited Γ'] (f : Turing.PointedMap Γ Γ')   (l : Turing.List
Blank Γ) (a : Γ…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Turing.ListBlank.head_map`：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inha
bited Γ] [inst_1 : Inhabited Γ'] (f : Turing.PointedMap Γ Γ')   (l : Turing.List
Blank Γ), (Turi…
· 使用定理 `Turing.ListBlank.tail_map`：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inha
bited Γ] [inst_1 : Inhabited Γ'] (f : Turing.PointedMap Γ Γ')   (l : Turing.List
Blank Γ), (Turi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ListBlank.map_modifyNth {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (F : PointedMap Γ Γ')
    (f : Γ → Γ) (f' : Γ' → Γ') (H : ∀ x, F (f x) = f' (F x)) (n) (L : ListBlank Γ) :
    (L.modifyNth f n).map F = (L.map F).modifyNth f' n := by
  induction n generalizing L <;>
    simp only [*, ListBlank.head_map, ListBlank.modifyNth, ListBlank.map_cons, ListBlank.tail_map]

/-- Append a list on the left side of a `ListBlank`. -/
@[simp]
/-
**Turing.ListBlank.append** 是 Mathlib 中的一个定义，位于命名空间 `Turing.ListBlank`。
形式化陈述：{Γ : Type u_1} → [inst : Inhabited Γ] → List Γ → Turing.ListBlank Γ → Turi
ng.ListBlank Γ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Append a list on the left side of a `ListBlank`.
-/
def ListBlank.append {Γ} [Inhabited Γ] : List Γ → ListBlank Γ → ListBlank Γ
  | [], L => L
  | a :: l, L => ListBlank.cons a (ListBlank.append l L)

@[simp]
/-
**Turing.ListBlank.append_mk** 是 Mathlib 中的一个定理，位于命名空间 `Turing.ListBlank`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (l₁ l₂ : List Γ),   Turing.ListBlank
.append l₁ (Turing.ListBlank.mk l₂) = Turing.ListBlank.mk (l₁ ++ l₂)
参数：l₁ l₂ : List Γ；Turing.ListBlank.mk l₂；l₁ ++ l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem ListBlank.append_mk {Γ} [Inhabited Γ] (l₁ l₂ : List Γ) :
    ListBlank.append l₁ (ListBlank.mk l₂) = ListBlank.mk (l₁ ++ l₂) := by
  induction l₁ <;>
    simp only [*, ListBlank.append, List.nil_append, List.cons_append, ListBlank.cons_mk]
/-
**Turing.ListBlank.append_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Turing.ListBlank`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (l₁ l₂ : List Γ) (l₃ : Turing.ListBl
ank Γ),   Turing.ListBlank.append (l₁ ++ l₂) l₃ = Turing.ListBlank.append l₁ (Tu
ring.ListBlank.append l₂ l₃)
参数：l₁ l₂ : List Γ；l₃ : Turing.ListBlank Γ；l₁ ++ l₂；Turing.ListBlank.append l₂ l₃
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.ListBlank.induction_on`：∀ {Γ : Type u_1} [inst : Inhabited Γ] {p 
: Turing.ListBlank Γ → Prop} (q : Turing.ListBlank Γ),   (∀ (a : List Γ), p (Tur
ing.ListBlank.mk a)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Turing.ListBlank.append_mk`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (l₁ l₂
 : List Γ),   Turing.ListBlank.append l₁ (Turing.ListBlank.mk l₂) = Turing.ListB
lank.mk (l₁ ++ l…
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ListBlank.append_assoc {Γ} [Inhabited Γ] (l₁ l₂ : List Γ) (l₃ : ListBlank Γ) :
    ListBlank.append (l₁ ++ l₂) l₃ = ListBlank.append l₁ (ListBlank.append l₂ l₃) := by
  refine l₃.induction_on fun l ↦ ?_
  simp only [ListBlank.append_mk, List.append_assoc]

/-- The `flatMap` function on lists is well defined on `ListBlank`s provided that the default
element is sent to a sequence of default elements. -/
/-
**Turing.ListBlank.flatMap** 是 Mathlib 中的一个定义，位于命名空间 `Turing.ListBlank`。
形式化陈述：{Γ : Type u_1} →   {Γ' : Type u_2} →     [inst : Inhabited Γ] →       [ins
t_1 : Inhabited Γ'] →         Turing.ListBlank Γ → (f : Γ → List Γ') → (∃ n, f d
efault = List.replicate n default) → Turing.ListBlank Γ'
参数：f : Γ → List Γ'；∃ n, f default = List.replicate n default。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `flatMap` function on lists is well defined on `ListBlank`s provided that th
e default
element is sent to a sequence of default elements.
-/
def ListBlank.flatMap {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (l : ListBlank Γ) (f : Γ → List Γ')
    (hf : ∃ n, f default = List.replicate n default) : ListBlank Γ' := by
  apply l.liftOn (fun l ↦ ListBlank.mk (l.flatMap f))
  rintro l _ ⟨i, rfl⟩; obtain ⟨n, e⟩ := hf; refine Quotient.sound' (Or.inl ⟨i * n, ?_⟩)
  rw [List.flatMap_append, mul_comm]; congr
  induction i with
  | zero => rfl
  | succ i IH =>
    simp only [IH, e, List.replicate_add, Nat.mul_succ, add_comm, List.replicate_succ,
      List.flatMap_cons]

@[simp]
/-
**Turing.ListBlank.flatMap_mk** 是 Mathlib 中的一个定理，位于命名空间 `Turing.ListBlank`。
形式化陈述：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inhabited Γ] [inst_1 : Inhabited 
Γ'] (l : List Γ) (f : Γ → List Γ')   (hf : ∃ n, f default = List.replicate n def
ault),   (Turing.ListBlank.mk l).flatMap f hf = Turing.ListBlank.mk (List.flatMa
p f l)
参数：l : List Γ；f : Γ → List Γ'；hf : ∃ n, f default = List.replicate n default；Tur
ing.ListBlank.mk l；List.flatMap f l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ListBlank.flatMap_mk
    {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (l : List Γ) (f : Γ → List Γ') (hf) :
    (ListBlank.mk l).flatMap f hf = ListBlank.mk (l.flatMap f) :=
  rfl

@[simp]
/-
**Turing.ListBlank.cons_flatMap** 是 Mathlib 中的一个定理，位于命名空间 `Turing.ListBlank`。
形式化陈述：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inhabited Γ] [inst_1 : Inhabited 
Γ'] (a : Γ) (l : Turing.ListBlank Γ)   (f : Γ → List Γ') (hf : ∃ n, f default = 
List.replicate n default),   (Turing.ListBlank.cons a l).flatMap f hf = Turing.L
istBlank.append (f a) (l.flatMap f hf)
参数：a : Γ；l : Turing.ListBlank Γ；f : Γ → List Γ'；hf : ∃ n, f default = List.repli
cate n default；Turing.ListBlank.cons a l；f a；l.flatMap f hf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.ListBlank.induction_on`：∀ {Γ : Type u_1} [inst : Inhabited Γ] {p 
: Turing.ListBlank Γ → Prop} (q : Turing.ListBlank Γ),   (∀ (a : List Γ), p (Tur
ing.ListBlank.mk a)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.flatMap_cons`：∀ {α : Type u} {β : Type v} {x : α} {xs : List α} {f 
: α → List β}, List.flatMap f (x :: xs) = f x ++ List.flatMap f xs
· 使用定理 `Turing.ListBlank.append_mk`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (l₁ l₂
 : List Γ),   Turing.ListBlank.append l₁ (Turing.ListBlank.mk l₂) = Turing.ListB
lank.mk (l₁ ++ l…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ListBlank.cons_flatMap {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (a : Γ) (l : ListBlank Γ)
    (f : Γ → List Γ') (hf) : (l.cons a).flatMap f hf = (l.flatMap f hf).append (f a) := by
  refine l.induction_on fun l ↦ ?_
  simp only [ListBlank.append_mk, ListBlank.flatMap_mk, ListBlank.cons_mk, List.flatMap_cons]

end ListBlank

section Tape

/-- The tape of a Turing machine is composed of a head element (which we imagine to be the
current position of the head), together with two `ListBlank`s denoting the portions of the tape
going off to the left and right. When the Turing machine moves right, an element is pulled from the
right side and becomes the new head, while the head element is `cons`ed onto the left side. -/
/-
**Turing.Tape** 是 Mathlib 中的一个归纳类型，位于命名空间 `Turing`。
形式化陈述：(Γ : Type u_1) → [Inhabited Γ] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tape of a Turing machine is composed of a head element (which we imagine to 
be the
current position of the head), together with two `ListBlank`s denoting the porti
ons of the tape
going off to the left and right. When the Turing machine moves right, an element
 is pulled from the
right side and becomes the new head, while the head element is `cons`ed onto the
 left side.
-/
structure Tape (Γ : Type*) [Inhabited Γ] where
  /-- The current position of the head. -/
  head : Γ
  /-- The portion of the tape going off to the left. -/
  left : ListBlank Γ
  /-- The portion of the tape going off to the right. -/
  right : ListBlank Γ
/-
**Turing.Tape.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `Turing.Tape`。
形式化陈述：{Γ : Type u_1} → [inst : Inhabited Γ] → Inhabited (Turing.Tape Γ)
参数：Turing.Tape Γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Tape.inhabited {Γ} [Inhabited Γ] : Inhabited (Tape Γ) :=
  ⟨by constructor <;> apply default⟩

/-- A direction for the Turing machine `move` command, either
  left or right. -/
/-
**Turing.Dir** 是 Mathlib 中的一个归纳类型，位于命名空间 `Turing`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A direction for the Turing machine `move` command, either
  left or right.
-/
inductive Dir
  | left
  | right
  deriving DecidableEq, Inhabited

/-- The "inclusive" left side of the tape, including both `left` and `head`. -/
/-
**Turing.Tape.left** 是 Mathlib 中的一个定义，位于命名空间 `Turing.Tape`。
形式化陈述：{Γ : Type u_1} → [inst : Inhabited Γ] → Turing.Tape Γ → Turing.ListBlank Γ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "inclusive" left side of the tape, including both `left` and `head`.
-/
def Tape.left₀ {Γ} [Inhabited Γ] (T : Tape Γ) : ListBlank Γ :=
  T.left.cons T.head

/-- The "inclusive" right side of the tape, including both `right` and `head`. -/
/-
**Turing.Tape.right** 是 Mathlib 中的一个定义，位于命名空间 `Turing.Tape`。
形式化陈述：{Γ : Type u_1} → [inst : Inhabited Γ] → Turing.Tape Γ → Turing.ListBlank Γ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "inclusive" right side of the tape, including both `right` and `head`.
-/
def Tape.right₀ {Γ} [Inhabited Γ] (T : Tape Γ) : ListBlank Γ :=
  T.right.cons T.head

/-- Move the tape in response to a motion of the Turing machine. Note that `T.move Dir.left` makes
`T.left` smaller; the Turing machine is moving left and the tape is moving right. -/
/-
**Turing.Tape.move** 是 Mathlib 中的一个定义，位于命名空间 `Turing.Tape`。
形式化陈述：{Γ : Type u_1} → [inst : Inhabited Γ] → Turing.Dir → Turing.Tape Γ → Turin
g.Tape Γ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Move the tape in response to a motion of the Turing machine. Note that `T.move D
ir.left` makes
`T.left` smaller; the Turing machine is moving left and the tape is moving right
.
-/
def Tape.move {Γ} [Inhabited Γ] : Dir → Tape Γ → Tape Γ
  | Dir.left, ⟨a, L, R⟩ => ⟨L.head, L.tail, R.cons a⟩
  | Dir.right, ⟨a, L, R⟩ => ⟨R.head, L.cons a, R.tail⟩

@[simp]
/-
**Turing.Tape.move_left_right** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Tape`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (T : Turing.Tape Γ),   Turing.Tape.m
ove Turing.Dir.right (Turing.Tape.move Turing.Dir.left T) = T
参数：T : Turing.Tape Γ；Turing.Tape.move Turing.Dir.left T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Turing.ListBlank.head_cons`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (a : Γ
) (l : Turing.ListBlank Γ), (Turing.ListBlank.cons a l).head = a
· 使用定理 `Turing.ListBlank.cons_head_tail`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (
l : Turing.ListBlank Γ), Turing.ListBlank.cons l.head l.tail = l
· 使用定理 `Turing.ListBlank.tail_cons`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (a : Γ
) (l : Turing.ListBlank Γ), (Turing.ListBlank.cons a l).tail = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Tape.move_left_right {Γ} [Inhabited Γ] (T : Tape Γ) :
    (T.move Dir.left).move Dir.right = T := by
  simp [Tape.move]

@[simp]
/-
**Turing.Tape.move_right_left** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Tape`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (T : Turing.Tape Γ),   Turing.Tape.m
ove Turing.Dir.left (Turing.Tape.move Turing.Dir.right T) = T
参数：T : Turing.Tape Γ；Turing.Tape.move Turing.Dir.right T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Turing.ListBlank.head_cons`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (a : Γ
) (l : Turing.ListBlank Γ), (Turing.ListBlank.cons a l).head = a
· 使用定理 `Turing.ListBlank.tail_cons`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (a : Γ
) (l : Turing.ListBlank Γ), (Turing.ListBlank.cons a l).tail = l
· 使用定理 `Turing.ListBlank.cons_head_tail`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (
l : Turing.ListBlank Γ), Turing.ListBlank.cons l.head l.tail = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Tape.move_right_left {Γ} [Inhabited Γ] (T : Tape Γ) :
    (T.move Dir.right).move Dir.left = T := by
  simp [Tape.move]

/-- Construct a tape from a left side and an inclusive right side. -/
/-
**Turing.Tape.mk'** 是 Mathlib 中的一个定义，位于命名空间 `Turing.Tape`。
形式化陈述：{Γ : Type u_1} → [inst : Inhabited Γ] → Turing.ListBlank Γ → Turing.ListBl
ank Γ → Turing.Tape Γ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a tape from a left side and an inclusive right side.
-/
def Tape.mk' {Γ} [Inhabited Γ] (L R : ListBlank Γ) : Tape Γ :=
  ⟨R.head, L, R.tail⟩

@[simp]
/-
**Turing.Tape.mk'_left** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Tape`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (L R : Turing.ListBlank Γ), (Turing.
Tape.mk' L R).left = L
参数：L R : Turing.ListBlank Γ；Turing.Tape.mk' L R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Tape.mk'_left {Γ} [Inhabited Γ] (L R : ListBlank Γ) : (Tape.mk' L R).left = L :=
  rfl

@[simp]
/-
**Turing.Tape.mk'_head** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Tape`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (L R : Turing.ListBlank Γ), (Turing.
Tape.mk' L R).head = R.head
参数：L R : Turing.ListBlank Γ；Turing.Tape.mk' L R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Tape.mk'_head {Γ} [Inhabited Γ] (L R : ListBlank Γ) : (Tape.mk' L R).head = R.head :=
  rfl

@[simp]
/-
**Turing.Tape.mk'_right** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Tape`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (L R : Turing.ListBlank Γ), (Turing.
Tape.mk' L R).right = R.tail
参数：L R : Turing.ListBlank Γ；Turing.Tape.mk' L R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Tape.mk'_right {Γ} [Inhabited Γ] (L R : ListBlank Γ) : (Tape.mk' L R).right = R.tail :=
  rfl

@[simp]
/-
**Turing.Tape.mk'_right** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Tape`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (L R : Turing.ListBlank Γ), (Turing.
Tape.mk' L R).right = R.tail
参数：L R : Turing.ListBlank Γ；Turing.Tape.mk' L R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Tape.mk'_right₀ {Γ} [Inhabited Γ] (L R : ListBlank Γ) : (Tape.mk' L R).right₀ = R :=
  ListBlank.cons_head_tail _

@[simp]
/-
**Turing.Tape.mk'_left_right** 是 Mathlib 中的一个定理，位于命名空间 `Turing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Tape.mk'_left_right₀ {Γ} [Inhabited Γ] (T : Tape Γ) : Tape.mk' T.left T.right₀ = T := by
  simp only [Tape.right₀, Tape.mk', ListBlank.head_cons, ListBlank.tail_cons]
/-
**Turing.Tape.exists_mk'** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Tape`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (T : Turing.Tape Γ), ∃ L R, T = Turi
ng.Tape.mk' L R
参数：T : Turing.Tape Γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Turing.Tape.mk'_left_right₀`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (T : 
Turing.Tape Γ), Turing.Tape.mk' T.left T.right₀ = T
-/
theorem Tape.exists_mk' {Γ} [Inhabited Γ] (T : Tape Γ) : ∃ L R, T = Tape.mk' L R :=
  ⟨_, _, (Tape.mk'_left_right₀ _).symm⟩

@[simp]
/-
**Turing.Tape.move_left_mk'** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Tape`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (L R : Turing.ListBlank Γ),   Turing
.Tape.move Turing.Dir.left (Turing.Tape.mk' L R) = Turing.Tape.mk' L.tail (Turin
g.ListBlank.cons L.head R)
参数：L R : Turing.ListBlank Γ；Turing.Tape.mk' L R；Turing.ListBlank.cons L.head R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Turing.ListBlank.cons_head_tail`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (
l : Turing.ListBlank Γ), Turing.ListBlank.cons l.head l.tail = l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Turing.ListBlank.head_cons`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (a : Γ
) (l : Turing.ListBlank Γ), (Turing.ListBlank.cons a l).head = a
· 使用定理 `Turing.ListBlank.tail_cons`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (a : Γ
) (l : Turing.ListBlank Γ), (Turing.ListBlank.cons a l).tail = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Tape.move_left_mk' {Γ} [Inhabited Γ] (L R : ListBlank Γ) :
    (Tape.mk' L R).move Dir.left = Tape.mk' L.tail (R.cons L.head) := by
  simp only [Tape.move, Tape.mk', ListBlank.head_cons, ListBlank.cons_head_tail,
    ListBlank.tail_cons]

@[simp]
/-
**Turing.Tape.move_right_mk'** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Tape`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (L R : Turing.ListBlank Γ),   Turing
.Tape.move Turing.Dir.right (Turing.Tape.mk' L R) = Turing.Tape.mk' (Turing.List
Blank.cons R.head L) R.tail
参数：L R : Turing.ListBlank Γ；Turing.Tape.mk' L R；Turing.ListBlank.cons R.head L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Tape.move_right_mk' {Γ} [Inhabited Γ] (L R : ListBlank Γ) :
    (Tape.mk' L R).move Dir.right = Tape.mk' (L.cons R.head) R.tail := by
  simp only [Tape.move, Tape.mk']

/-- Construct a tape from a left side and an inclusive right side. -/
/-
**Turing.Tape.mk** 是 Mathlib 中的一个ctor，位于命名空间 `Turing.Tape`。
形式化陈述：{Γ : Type u_1} → [inst : Inhabited Γ] → Γ → Turing.ListBlank Γ → Turing.Li
stBlank Γ → Turing.Tape Γ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a tape from a left side and an inclusive right side.
-/
def Tape.mk₂ {Γ} [Inhabited Γ] (L R : List Γ) : Tape Γ :=
  Tape.mk' (ListBlank.mk L) (ListBlank.mk R)

/-- Construct a tape from a list, with the head of the list at the TM head and the rest going
to the right. -/
/-
**Turing.Tape.mk** 是 Mathlib 中的一个ctor，位于命名空间 `Turing.Tape`。
形式化陈述：{Γ : Type u_1} → [inst : Inhabited Γ] → Γ → Turing.ListBlank Γ → Turing.Li
stBlank Γ → Turing.Tape Γ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a tape from a list, with the head of the list at the TM head and the r
est going
to the right.
-/
def Tape.mk₁ {Γ} [Inhabited Γ] (l : List Γ) : Tape Γ :=
  Tape.mk₂ [] l

/-- The `nth` function of a tape is integer-valued, with index `0` being the head, negative indexes
on the left and positive indexes on the right. (Picture a number line.) -/
/-
**Turing.Tape.nth** 是 Mathlib 中的一个定义，位于命名空间 `Turing.Tape`。
形式化陈述：{Γ : Type u_1} → [inst : Inhabited Γ] → Turing.Tape Γ → ℤ → Γ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `nth` function of a tape is integer-valued, with index `0` being the head, n
egative indexes
on the left and positive indexes on the right. (Picture a number line.)
-/
def Tape.nth {Γ} [Inhabited Γ] (T : Tape Γ) : ℤ → Γ
  | 0 => T.head
  | (n + 1 : ℕ) => T.right.nth n
  | -(n + 1 : ℕ) => T.left.nth n

@[simp]
/-
**Turing.Tape.nth_zero** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Tape`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (T : Turing.Tape Γ), T.nth 0 = T.hea
d
参数：T : Turing.Tape Γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Tape.nth_zero {Γ} [Inhabited Γ] (T : Tape Γ) : T.nth 0 = T.1 :=
  rfl
/-
**Turing.Tape.right** 是 Mathlib 中的一个定义，位于命名空间 `Turing.Tape`。
形式化陈述：{Γ : Type u_1} → [inst : Inhabited Γ] → Turing.Tape Γ → Turing.ListBlank Γ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Tape.right₀_nth {Γ} [Inhabited Γ] (T : Tape Γ) (n : ℕ) : T.right₀.nth n = T.nth n := by
  cases n <;> simp only [Tape.nth, Tape.right₀, ListBlank.nth_zero,
    ListBlank.nth_succ, ListBlank.head_cons, ListBlank.tail_cons]

@[simp]
/-
**Turing.Tape.mk'_nth_nat** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Tape`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (L R : Turing.ListBlank Γ) (n : ℕ), 
(Turing.Tape.mk' L R).nth ↑n = R.nth n
参数：L R : Turing.ListBlank Γ；n : ℕ；Turing.Tape.mk' L R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Turing.Tape.right₀_nth`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (T : Turin
g.Tape Γ) (n : ℕ), T.right₀.nth n = T.nth ↑n
· 使用定理 `Turing.Tape.mk'_right₀`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (L R : Tur
ing.ListBlank Γ), (Turing.Tape.mk' L R).right₀ = R
-/
theorem Tape.mk'_nth_nat {Γ} [Inhabited Γ] (L R : ListBlank Γ) (n : ℕ) :
    (Tape.mk' L R).nth n = R.nth n := by
  rw [← Tape.right₀_nth, Tape.mk'_right₀]

@[simp]
/-
**Turing.Tape.move_left_nth** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Tape`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (T : Turing.Tape Γ) (i : ℤ),   (Turi
ng.Tape.move Turing.Dir.left T).nth i = T.nth (i - 1)
参数：T : Turing.Tape Γ；i : ℤ；Turing.Tape.move Turing.Dir.left T；i - 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Turing.ListBlank.nth_succ`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (l : Tu
ring.ListBlank Γ) (n : ℕ), l.nth (n + 1) = l.tail.nth n
· 使用定理 `Turing.ListBlank.nth_zero`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (l : Tu
ring.ListBlank Γ), l.nth 0 = l.head
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Turing.ListBlank.head_cons`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (a : Γ
) (l : Turing.ListBlank Γ), (Turing.ListBlank.cons a l).head = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `Turing.ListBlank.tail_cons`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (a : Γ
) (l : Turing.ListBlank Γ), (Turing.ListBlank.cons a l).tail = l
-/
theorem Tape.move_left_nth {Γ} [Inhabited Γ] :
    ∀ (T : Tape Γ) (i : ℤ), (T.move Dir.left).nth i = T.nth (i - 1)
  | ⟨_, _, _⟩, -(_ + 1 : ℕ) => (ListBlank.nth_succ _ _).symm
  | ⟨_, _, _⟩, 0 => (ListBlank.nth_zero _).symm
  | ⟨_, _, _⟩, 1 => (ListBlank.nth_zero _).trans (ListBlank.head_cons _ _)
  | ⟨a, L, R⟩, (n + 1 : ℕ) + 1 => by
    rw [add_sub_cancel_right]
    change (R.cons a).nth (n + 1) = R.nth n
    rw [ListBlank.nth_succ, ListBlank.tail_cons]

@[simp]
/-
**Turing.Tape.move_right_nth** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Tape`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (T : Turing.Tape Γ) (i : ℤ),   (Turi
ng.Tape.move Turing.Dir.right T).nth i = T.nth (i + 1)
参数：T : Turing.Tape Γ；i : ℤ；Turing.Tape.move Turing.Dir.right T；i + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Turing.Tape.move_right_left`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (T : 
Turing.Tape Γ),   Turing.Tape.move Turing.Dir.left (Turing.Tape.move Turing.Dir.
right T) = T
· 使用定理 `Turing.Tape.move_left_nth`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (T : Tu
ring.Tape Γ) (i : ℤ),   (Turing.Tape.move Turing.Dir.left T).nth i = T.nth (i - 
1)
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
-/
theorem Tape.move_right_nth {Γ} [Inhabited Γ] (T : Tape Γ) (i : ℤ) :
    (T.move Dir.right).nth i = T.nth (i + 1) := by
  conv => rhs; rw [← T.move_right_left]
  rw [Tape.move_left_nth, add_sub_cancel_right]

@[simp]
/-
**Turing.Tape.move_right_n_head** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Tape`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (T : Turing.Tape Γ) (i : ℕ),   ((Tur
ing.Tape.move Turing.Dir.right)^[i] T).head = T.nth ↑i
参数：T : Turing.Tape Γ；i : ℕ；(Turing.Tape.move Turing.Dir.right)^[i] T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Turing.Tape.move_right_nth`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (T : T
uring.Tape Γ) (i : ℤ),   (Turing.Tape.move Turing.Dir.right T).nth i = T.nth (i 
+ 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Tape.move_right_n_head {Γ} [Inhabited Γ] (T : Tape Γ) (i : ℕ) :
    ((Tape.move Dir.right)^[i] T).head = T.nth i := by
  induction i generalizing T
  · rfl
  · simp only [*, Tape.move_right_nth, Int.natCast_succ, iterate_succ, Function.comp_apply]

/-- Replace the current value of the head on the tape. -/
/-
**Turing.Tape.write** 是 Mathlib 中的一个定义，位于命名空间 `Turing.Tape`。
形式化陈述：{Γ : Type u_1} → [inst : Inhabited Γ] → Γ → Turing.Tape Γ → Turing.Tape Γ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Replace the current value of the head on the tape.
-/
def Tape.write {Γ} [Inhabited Γ] (b : Γ) (T : Tape Γ) : Tape Γ :=
  { T with head := b }

@[simp]
/-
**Turing.Tape.write_self** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Tape`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (T : Turing.Tape Γ), Turing.Tape.wri
te T.head T = T
参数：T : Turing.Tape Γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Tape.write_self {Γ} [Inhabited Γ] : ∀ T : Tape Γ, T.write T.1 = T := by
  rintro ⟨⟩; rfl

@[simp]
/-
**Turing.Tape.write_nth** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Tape`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (b : Γ) (T : Turing.Tape Γ) {i : ℤ},
   (Turing.Tape.write b T).nth i = if i = 0 then b else T.nth i
参数：b : Γ；T : Turing.Tape Γ；Turing.Tape.write b T。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Tape.write_nth {Γ} [Inhabited Γ] (b : Γ) :
    ∀ (T : Tape Γ) {i : ℤ}, (T.write b).nth i = if i = 0 then b else T.nth i
  | _, 0 => rfl
  | _, (_ + 1 : ℕ) => rfl
  | _, -(_ + 1 : ℕ) => rfl

@[simp]
/-
**Turing.Tape.write_mk** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Tape`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (a b : Γ) (L R : Turing.ListBlank Γ)
,   Turing.Tape.write b { head := a, left := L, right := R } = { head := b, left
 := L, right := R }
参数：a b : Γ；L R : Turing.ListBlank Γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Tape.write_mk {Γ} [Inhabited Γ] (a b : Γ) (L R : ListBlank Γ) :
    (mk a L R).write b = mk b L R := rfl

@[simp]
/-
**Turing.Tape.write_mk'** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Tape`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (b : Γ) (L R : Turing.ListBlank Γ), 
  Turing.Tape.write b (Turing.Tape.mk' L R) = Turing.Tape.mk' L (Turing.ListBlan
k.cons b R.tail)
参数：b : Γ；L R : Turing.ListBlank Γ；Turing.Tape.mk' L R；Turing.ListBlank.cons b R.
tail。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Turing.ListBlank.head_cons`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (a : Γ
) (l : Turing.ListBlank Γ), (Turing.ListBlank.cons a l).head = a
· 使用定理 `Turing.ListBlank.tail_cons`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (a : Γ
) (l : Turing.ListBlank Γ), (Turing.ListBlank.cons a l).tail = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Tape.write_mk' {Γ} [Inhabited Γ] (b : Γ) (L R : ListBlank Γ) :
    (mk' L R).write b = mk' L (R.tail.cons b) := by simp [mk']

/-- Apply a pointed map to a tape to change the alphabet. -/
/-
**Turing.Tape.map** 是 Mathlib 中的一个定义，位于命名空间 `Turing.Tape`。
形式化陈述：{Γ : Type u_1} →   {Γ' : Type u_2} →     [inst : Inhabited Γ] → [inst_1 : 
Inhabited Γ'] → Turing.PointedMap Γ Γ' → Turing.Tape Γ → Turing.Tape Γ'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Apply a pointed map to a tape to change the alphabet.
-/
def Tape.map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (T : Tape Γ) : Tape Γ' :=
  ⟨f T.1, T.2.map f, T.3.map f⟩

@[simp]
/-
**Turing.Tape.map_fst** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Tape`。
形式化陈述：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inhabited Γ] [inst_1 : Inhabited 
Γ'] (f : Turing.PointedMap Γ Γ')   (T : Turing.Tape Γ), (Turing.Tape.map f T).he
ad = f.f T.head
参数：f : Turing.PointedMap Γ Γ'；T : Turing.Tape Γ；Turing.Tape.map f T。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Tape.map_fst {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') :
    ∀ T : Tape Γ, (T.map f).1 = f T.1 := by
  rintro ⟨⟩; rfl

@[simp]
/-
**Turing.Tape.map_write** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Tape`。
形式化陈述：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inhabited Γ] [inst_1 : Inhabited 
Γ'] (f : Turing.PointedMap Γ Γ') (b : Γ)   (T : Turing.Tape Γ), Turing.Tape.map 
f (Turing.Tape.write b T) = Turing.Tape.write (f.f b) (Turing.Tape.map f T)
参数：f : Turing.PointedMap Γ Γ'；b : Γ；T : Turing.Tape Γ；Turing.Tape.write b T；f.f 
b；Turing.Tape.map f T。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Tape.map_write {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (b : Γ) :
    ∀ T : Tape Γ, (T.write b).map f = (T.map f).write (f b) := by
  rintro ⟨⟩; rfl

@[simp]
/-
**Turing.Tape.write_move_right_n** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Tape`。
形式化陈述：∀ {Γ : Type u_1} [inst : Inhabited Γ] (f : Γ → Γ) (L R : Turing.ListBlank 
Γ) (n : ℕ),   Turing.Tape.write (f (R.nth n)) ((Turing.Tape.move Turing.Dir.righ
t)^[n] (Turing.Tape.mk' L R)) =     (Turing.Tape.move Turing.Dir.right)^[n] (Tur
ing.Tape.mk' L (Turing.ListBlank.modifyNth f n R))
参数：f : Γ → Γ；L R : Turing.ListBlank Γ；n : ℕ；f (R.nth n)；(Turing.Tape.move Turing
.Dir.right)^[n] (Turing.Tape.mk' L R)；Turing.Tape.move Turing.Dir.right；Turing.T
ape.mk' L (Turing.ListBlank.modifyNth f n R)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Turing.ListBlank.nth_zero`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (l : Tu
ring.ListBlank Γ), l.nth 0 = l.head
· 使用定理 `Turing.Tape.write_mk'`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (b : Γ) (L 
R : Turing.ListBlank Γ),   Turing.Tape.write b (Turing.Tape.mk' L R) = Turing.Ta
pe.mk' L (T…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Turing.ListBlank.nth_succ`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (l : Tu
ring.ListBlank Γ) (n : ℕ), l.nth (n + 1) = l.tail.nth n
· 使用定理 `Turing.Tape.move_right_mk'`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (L R :
 Turing.ListBlank Γ),   Turing.Tape.move Turing.Dir.right (Turing.Tape.mk' L R) 
= Turing.Tape.mk…
· 使用定理 `Turing.ListBlank.head_cons`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (a : Γ
) (l : Turing.ListBlank Γ), (Turing.ListBlank.cons a l).head = a
· 使用定理 `Turing.ListBlank.tail_cons`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (a : Γ
) (l : Turing.ListBlank Γ), (Turing.ListBlank.cons a l).tail = l
-/
theorem Tape.write_move_right_n {Γ} [Inhabited Γ] (f : Γ → Γ) (L R : ListBlank Γ) (n : ℕ) :
    ((Tape.move Dir.right)^[n] (Tape.mk' L R)).write (f (R.nth n)) =
      (Tape.move Dir.right)^[n] (Tape.mk' L (R.modifyNth f n)) := by
  induction n generalizing L R <;> simp [*]
/-
**Turing.Tape.map_move** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Tape`。
形式化陈述：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inhabited Γ] [inst_1 : Inhabited 
Γ'] (f : Turing.PointedMap Γ Γ')   (T : Turing.Tape Γ) (d : Turing.Dir),   Turin
g.Tape.map f (Turing.Tape.move d T) = Turing.Tape.move d (Turing.Tape.map f T)
参数：f : Turing.PointedMap Γ Γ'；T : Turing.Tape Γ；d : Turing.Dir；Turing.Tape.move 
d T；Turing.Tape.map f T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Turing.ListBlank.map_cons`：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inha
bited Γ] [inst_1 : Inhabited Γ'] (f : Turing.PointedMap Γ Γ')   (l : Turing.List
Blank Γ) (a : Γ…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Turing.ListBlank.head_map`：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inha
bited Γ] [inst_1 : Inhabited Γ'] (f : Turing.PointedMap Γ Γ')   (l : Turing.List
Blank Γ), (Turi…
· 使用定理 `Turing.ListBlank.tail_map`：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inha
bited Γ] [inst_1 : Inhabited Γ'] (f : Turing.PointedMap Γ Γ')   (l : Turing.List
Blank Γ), (Turi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Tape.map_move {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (T : Tape Γ) (d) :
    (T.move d).map f = (T.map f).move d := by
  cases T
  cases d <;> simp only [Tape.move, Tape.map, ListBlank.head_map,
    ListBlank.map_cons, ListBlank.tail_map]
/-
**Turing.Tape.map_mk'** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Tape`。
形式化陈述：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inhabited Γ] [inst_1 : Inhabited 
Γ'] (f : Turing.PointedMap Γ Γ')   (L R : Turing.ListBlank Γ),   Turing.Tape.map
 f (Turing.Tape.mk' L R) = Turing.Tape.mk' (Turing.ListBlank.map f L) (Turing.Li
stBlank.map f R)
参数：f : Turing.PointedMap Γ Γ'；L R : Turing.ListBlank Γ；Turing.Tape.mk' L R；Turin
g.ListBlank.map f L；Turing.ListBlank.map f R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Turing.ListBlank.head_map`：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inha
bited Γ] [inst_1 : Inhabited Γ'] (f : Turing.PointedMap Γ Γ')   (l : Turing.List
Blank Γ), (Turi…
· 使用定理 `Turing.ListBlank.tail_map`：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inha
bited Γ] [inst_1 : Inhabited Γ'] (f : Turing.PointedMap Γ Γ')   (l : Turing.List
Blank Γ), (Turi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Tape.map_mk' {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (L R : ListBlank Γ) :
    (Tape.mk' L R).map f = Tape.mk' (L.map f) (R.map f) := by
  simp only [Tape.mk', Tape.map, ListBlank.head_map,
    ListBlank.tail_map]
/-
**Turing.Tape.map_mk** 是 Mathlib 中的一个定理，位于命名空间 `Turing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Tape.map_mk₂ {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (L R : List Γ) :
    (Tape.mk₂ L R).map f = Tape.mk₂ (L.map f) (R.map f) := by
  simp only [Tape.mk₂, Tape.map_mk', ListBlank.map_mk]
/-
**Turing.Tape.map_mk** 是 Mathlib 中的一个定理，位于命名空间 `Turing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Tape.map_mk₁ {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (l : List Γ) :
    (Tape.mk₁ l).map f = Tape.mk₁ (l.map f) :=
  Tape.map_mk₂ _ _ _

end Tape

end Turing

