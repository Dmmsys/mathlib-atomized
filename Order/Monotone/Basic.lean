/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Yaël Dillies
-/
module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.Compare
public import Mathlib.Order.Max
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Contrapose

/-!
# Monotonicity

This file defines (strictly) monotone/antitone functions. Contrary to standard mathematical usage,
"monotone"/"mono" here means "increasing", not "increasing or decreasing". We use "antitone"/"anti"
to mean "decreasing".

## Main theorems

* `monotone_nat_of_le_succ`, `monotone_int_of_le_succ`: If `f : ℕ → α` or `f : ℤ → α` and
  `f n ≤ f (n + 1)` for all `n`, then `f` is monotone.
* `antitone_nat_of_succ_le`, `antitone_int_of_succ_le`: If `f : ℕ → α` or `f : ℤ → α` and
  `f (n + 1) ≤ f n` for all `n`, then `f` is antitone.
* `strictMono_nat_of_lt_succ`, `strictMono_int_of_lt_succ`: If `f : ℕ → α` or `f : ℤ → α` and
  `f n < f (n + 1)` for all `n`, then `f` is strictly monotone.
* `strictAnti_nat_of_succ_lt`, `strictAnti_int_of_succ_lt`: If `f : ℕ → α` or `f : ℤ → α` and
  `f (n + 1) < f n` for all `n`, then `f` is strictly antitone.

## Implementation notes

Some of these definitions used to only require `LE α` or `LT α`. The advantage of this is
unclear and it led to slight elaboration issues. Now, everything requires `Preorder α` and seems to
work fine. Related Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Order.20diamond/near/254353352.

## TODO

The above theorems are also true in `ℕ+`, `Fin n`... To make that work, we need `SuccOrder α`
and `IsSuccArchimedean α`.

## Tags

monotone, strictly monotone, antitone, strictly antitone, increasing, strictly increasing,
decreasing, strictly decreasing
-/

public section

open Function OrderDual

universe u v

variable {ι : Type*} {α : Type u} {β : Type v}

/-! ### Monotonicity on the dual order

Strictly, many of the `*On.dual` lemmas in this section should use `ofDual ⁻¹' s` instead of `s`,
but right now this is not possible as `Set.preimage` is not defined yet, and importing it creates
an import cycle.

Often, you should not need the rewriting lemmas. Instead, you probably want to add `.dual`,
`.dual_left` or `.dual_right` to your `Monotone`/`Antitone` hypothesis.
-/


section OrderDual

variable [Preorder α] [Preorder β] {f : α → β} {s : Set α}

@[simp]
/-
**monotone_comp_ofDual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_comp_ofDual_iff : Monotone (f ∘ ofDual) ↔ Antitone f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
theorem monotone_comp_ofDual_iff : Monotone (f ∘ ofDual) ↔ Antitone f :=
  forall_comm

@[simp]
/-
**antitone_comp_ofDual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitone_comp_ofDual_iff : Antitone (f ∘ ofDual) ↔ Monotone f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
theorem antitone_comp_ofDual_iff : Antitone (f ∘ ofDual) ↔ Monotone f :=
  forall_comm

@[simp]
/-
**monotone_toDual_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_toDual_comp_iff : Monotone (toDual ∘ f) ↔ Antitone f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem monotone_toDual_comp_iff : Monotone (toDual ∘ f) ↔ Antitone f :=
  Iff.rfl

@[simp]
/-
**antitone_toDual_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitone_toDual_comp_iff : Antitone (toDual ∘ f) ↔ Monotone f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem antitone_toDual_comp_iff : Antitone (toDual ∘ f) ↔ Monotone f :=
  Iff.rfl

@[simp]
/-
**monotoneOn_comp_ofDual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotoneOn_comp_ofDual_iff : MonotoneOn (f ∘ ofDual) s ↔ AntitoneOn f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_comm`：forall₂_comm {ι₁ ι₂ : Sort*} {κ₁ : ι₁ -> Sort*} {κ₂ : ι₂ -
> Sort*} {p : forall i₁, κ₁ i₁ -> forall i₂, κ₂ i₂ -> Prop} : (forall i₁ j₁ i₂ j
₂,…
-/
theorem monotoneOn_comp_ofDual_iff : MonotoneOn (f ∘ ofDual) s ↔ AntitoneOn f s :=
  forall₂_comm

@[simp]
/-
**antitoneOn_comp_ofDual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitoneOn_comp_ofDual_iff : AntitoneOn (f ∘ ofDual) s ↔ MonotoneOn f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_comm`：forall₂_comm {ι₁ ι₂ : Sort*} {κ₁ : ι₁ -> Sort*} {κ₂ : ι₂ -
> Sort*} {p : forall i₁, κ₁ i₁ -> forall i₂, κ₂ i₂ -> Prop} : (forall i₁ j₁ i₂ j
₂,…
-/
theorem antitoneOn_comp_ofDual_iff : AntitoneOn (f ∘ ofDual) s ↔ MonotoneOn f s :=
  forall₂_comm

@[simp]
/-
**monotoneOn_toDual_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotoneOn_toDual_comp_iff : MonotoneOn (toDual ∘ f) s ↔ AntitoneOn f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem monotoneOn_toDual_comp_iff : MonotoneOn (toDual ∘ f) s ↔ AntitoneOn f s :=
  Iff.rfl

@[simp]
/-
**antitoneOn_toDual_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitoneOn_toDual_comp_iff : AntitoneOn (toDual ∘ f) s ↔ MonotoneOn f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem antitoneOn_toDual_comp_iff : AntitoneOn (toDual ∘ f) s ↔ MonotoneOn f s :=
  Iff.rfl

@[simp]
/-
**strictMono_comp_ofDual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictMono_comp_ofDual_iff : StrictMono (f ∘ ofDual) ↔ StrictAnti f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
theorem strictMono_comp_ofDual_iff : StrictMono (f ∘ ofDual) ↔ StrictAnti f :=
  forall_comm

@[simp]
/-
**strictAnti_comp_ofDual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictAnti_comp_ofDual_iff : StrictAnti (f ∘ ofDual) ↔ StrictMono f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
theorem strictAnti_comp_ofDual_iff : StrictAnti (f ∘ ofDual) ↔ StrictMono f :=
  forall_comm

@[simp]
/-
**strictMono_toDual_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictMono_toDual_comp_iff : StrictMono (toDual ∘ f : α -> βᵒᵈ) ↔ StrictAn
ti f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem strictMono_toDual_comp_iff : StrictMono (toDual ∘ f : α → βᵒᵈ) ↔ StrictAnti f :=
  Iff.rfl

@[simp]
/-
**strictAnti_toDual_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictAnti_toDual_comp_iff : StrictAnti (toDual ∘ f : α -> βᵒᵈ) ↔ StrictMo
no f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem strictAnti_toDual_comp_iff : StrictAnti (toDual ∘ f : α → βᵒᵈ) ↔ StrictMono f :=
  Iff.rfl

@[simp]
/-
**strictMonoOn_comp_ofDual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictMonoOn_comp_ofDual_iff : StrictMonoOn (f ∘ ofDual) s ↔ StrictAntiOn 
f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_comm`：forall₂_comm {ι₁ ι₂ : Sort*} {κ₁ : ι₁ -> Sort*} {κ₂ : ι₂ -
> Sort*} {p : forall i₁, κ₁ i₁ -> forall i₂, κ₂ i₂ -> Prop} : (forall i₁ j₁ i₂ j
₂,…
-/
theorem strictMonoOn_comp_ofDual_iff : StrictMonoOn (f ∘ ofDual) s ↔ StrictAntiOn f s :=
  forall₂_comm

@[simp]
/-
**strictAntiOn_comp_ofDual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictAntiOn_comp_ofDual_iff : StrictAntiOn (f ∘ ofDual) s ↔ StrictMonoOn 
f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_comm`：forall₂_comm {ι₁ ι₂ : Sort*} {κ₁ : ι₁ -> Sort*} {κ₂ : ι₂ -
> Sort*} {p : forall i₁, κ₁ i₁ -> forall i₂, κ₂ i₂ -> Prop} : (forall i₁ j₁ i₂ j
₂,…
-/
theorem strictAntiOn_comp_ofDual_iff : StrictAntiOn (f ∘ ofDual) s ↔ StrictMonoOn f s :=
  forall₂_comm

@[simp]
/-
**strictMonoOn_toDual_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictMonoOn_toDual_comp_iff : StrictMonoOn (toDual ∘ f : α -> βᵒᵈ) s ↔ St
rictAntiOn f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem strictMonoOn_toDual_comp_iff : StrictMonoOn (toDual ∘ f : α → βᵒᵈ) s ↔ StrictAntiOn f s :=
  Iff.rfl

@[simp]
/-
**strictAntiOn_toDual_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictAntiOn_toDual_comp_iff : StrictAntiOn (toDual ∘ f : α -> βᵒᵈ) s ↔ St
rictMonoOn f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem strictAntiOn_toDual_comp_iff : StrictAntiOn (toDual ∘ f : α → βᵒᵈ) s ↔ StrictMonoOn f s :=
  Iff.rfl
/-
**monotone_dual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_dual_iff : Monotone (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ) ↔ Monotone
 f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `monotone_toDual_comp_iff`：monotone_toDual_comp_iff : Monotone (toDual ∘ 
f) ↔ Antitone f
· 使用定理 `antitone_comp_ofDual_iff`：antitone_comp_ofDual_iff : Antitone (f ∘ ofDua
l) ↔ Monotone f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem monotone_dual_iff : Monotone (toDual ∘ f ∘ ofDual : αᵒᵈ → βᵒᵈ) ↔ Monotone f := by
  rw [monotone_toDual_comp_iff, antitone_comp_ofDual_iff]
/-
**antitone_dual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitone_dual_iff : Antitone (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ) ↔ Antitone
 f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `antitone_toDual_comp_iff`：antitone_toDual_comp_iff : Antitone (toDual ∘ 
f) ↔ Monotone f
· 使用定理 `monotone_comp_ofDual_iff`：monotone_comp_ofDual_iff : Monotone (f ∘ ofDua
l) ↔ Antitone f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem antitone_dual_iff : Antitone (toDual ∘ f ∘ ofDual : αᵒᵈ → βᵒᵈ) ↔ Antitone f := by
  rw [antitone_toDual_comp_iff, monotone_comp_ofDual_iff]

set_option backward.isDefEq.respectTransparency false in
/-
**monotoneOn_dual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotoneOn_dual_iff : MonotoneOn (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ) s ↔ Mo
notoneOn f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `monotoneOn_toDual_comp_iff`：monotoneOn_toDual_comp_iff : MonotoneOn (toD
ual ∘ f) s ↔ AntitoneOn f s
· 使用定理 `antitoneOn_comp_ofDual_iff`：antitoneOn_comp_ofDual_iff : AntitoneOn (f ∘
 ofDual) s ↔ MonotoneOn f s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem monotoneOn_dual_iff : MonotoneOn (toDual ∘ f ∘ ofDual : αᵒᵈ → βᵒᵈ) s ↔ MonotoneOn f s := by
  rw [monotoneOn_toDual_comp_iff, antitoneOn_comp_ofDual_iff]

set_option backward.isDefEq.respectTransparency false in
/-
**antitoneOn_dual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitoneOn_dual_iff : AntitoneOn (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ) s ↔ An
titoneOn f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `antitoneOn_toDual_comp_iff`：antitoneOn_toDual_comp_iff : AntitoneOn (toD
ual ∘ f) s ↔ MonotoneOn f s
· 使用定理 `monotoneOn_comp_ofDual_iff`：monotoneOn_comp_ofDual_iff : MonotoneOn (f ∘
 ofDual) s ↔ AntitoneOn f s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem antitoneOn_dual_iff : AntitoneOn (toDual ∘ f ∘ ofDual : αᵒᵈ → βᵒᵈ) s ↔ AntitoneOn f s := by
  rw [antitoneOn_toDual_comp_iff, monotoneOn_comp_ofDual_iff]
/-
**strictMono_dual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictMono_dual_iff : StrictMono (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ) ↔ Stri
ctMono f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `strictMono_toDual_comp_iff`：strictMono_toDual_comp_iff : StrictMono (toD
ual ∘ f : α -> βᵒᵈ) ↔ StrictAnti f
· 使用定理 `strictAnti_comp_ofDual_iff`：strictAnti_comp_ofDual_iff : StrictAnti (f ∘
 ofDual) ↔ StrictMono f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem strictMono_dual_iff : StrictMono (toDual ∘ f ∘ ofDual : αᵒᵈ → βᵒᵈ) ↔ StrictMono f := by
  rw [strictMono_toDual_comp_iff, strictAnti_comp_ofDual_iff]
/-
**strictAnti_dual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictAnti_dual_iff : StrictAnti (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ) ↔ Stri
ctAnti f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `strictAnti_toDual_comp_iff`：strictAnti_toDual_comp_iff : StrictAnti (toD
ual ∘ f : α -> βᵒᵈ) ↔ StrictMono f
· 使用定理 `strictMono_comp_ofDual_iff`：strictMono_comp_ofDual_iff : StrictMono (f ∘
 ofDual) ↔ StrictAnti f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem strictAnti_dual_iff : StrictAnti (toDual ∘ f ∘ ofDual : αᵒᵈ → βᵒᵈ) ↔ StrictAnti f := by
  rw [strictAnti_toDual_comp_iff, strictMono_comp_ofDual_iff]

set_option backward.isDefEq.respectTransparency false in
/-
**strictMonoOn_dual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictMonoOn_dual_iff : StrictMonoOn (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ) s 
↔ StrictMonoOn f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `strictMonoOn_toDual_comp_iff`：strictMonoOn_toDual_comp_iff : StrictMonoO
n (toDual ∘ f : α -> βᵒᵈ) s ↔ StrictAntiOn f s
· 使用定理 `strictAntiOn_comp_ofDual_iff`：strictAntiOn_comp_ofDual_iff : StrictAntiO
n (f ∘ ofDual) s ↔ StrictMonoOn f s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem strictMonoOn_dual_iff :
    StrictMonoOn (toDual ∘ f ∘ ofDual : αᵒᵈ → βᵒᵈ) s ↔ StrictMonoOn f s := by
  rw [strictMonoOn_toDual_comp_iff, strictAntiOn_comp_ofDual_iff]

set_option backward.isDefEq.respectTransparency false in
/-
**strictAntiOn_dual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictAntiOn_dual_iff : StrictAntiOn (toDual ∘ f ∘ ofDual : αᵒᵈ -> βᵒᵈ) s 
↔ StrictAntiOn f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `strictAntiOn_toDual_comp_iff`：strictAntiOn_toDual_comp_iff : StrictAntiO
n (toDual ∘ f : α -> βᵒᵈ) s ↔ StrictMonoOn f s
· 使用定理 `strictMonoOn_comp_ofDual_iff`：strictMonoOn_comp_ofDual_iff : StrictMonoO
n (f ∘ ofDual) s ↔ StrictAntiOn f s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem strictAntiOn_dual_iff :
    StrictAntiOn (toDual ∘ f ∘ ofDual : αᵒᵈ → βᵒᵈ) s ↔ StrictAntiOn f s := by
  rw [strictAntiOn_toDual_comp_iff, strictMonoOn_comp_ofDual_iff]

alias ⟨_, Monotone.dual_left⟩ := antitone_comp_ofDual_iff

alias ⟨_, Antitone.dual_left⟩ := monotone_comp_ofDual_iff

alias ⟨_, Monotone.dual_right⟩ := antitone_toDual_comp_iff

alias ⟨_, Antitone.dual_right⟩ := monotone_toDual_comp_iff

alias ⟨_, MonotoneOn.dual_left⟩ := antitoneOn_comp_ofDual_iff

alias ⟨_, AntitoneOn.dual_left⟩ := monotoneOn_comp_ofDual_iff

alias ⟨_, MonotoneOn.dual_right⟩ := antitoneOn_toDual_comp_iff

alias ⟨_, AntitoneOn.dual_right⟩ := monotoneOn_toDual_comp_iff

alias ⟨_, StrictMono.dual_left⟩ := strictAnti_comp_ofDual_iff

alias ⟨_, StrictAnti.dual_left⟩ := strictMono_comp_ofDual_iff

alias ⟨_, StrictMono.dual_right⟩ := strictAnti_toDual_comp_iff

alias ⟨_, StrictAnti.dual_right⟩ := strictMono_toDual_comp_iff

alias ⟨_, StrictMonoOn.dual_left⟩ := strictAntiOn_comp_ofDual_iff

alias ⟨_, StrictAntiOn.dual_left⟩ := strictMonoOn_comp_ofDual_iff

alias ⟨_, StrictMonoOn.dual_right⟩ := strictAntiOn_toDual_comp_iff

alias ⟨_, StrictAntiOn.dual_right⟩ := strictMonoOn_toDual_comp_iff

alias ⟨_, Monotone.dual⟩ := monotone_dual_iff

alias ⟨_, Antitone.dual⟩ := antitone_dual_iff

alias ⟨_, MonotoneOn.dual⟩ := monotoneOn_dual_iff

alias ⟨_, AntitoneOn.dual⟩ := antitoneOn_dual_iff

alias ⟨_, StrictMono.dual⟩ := strictMono_dual_iff

alias ⟨_, StrictAnti.dual⟩ := strictAnti_dual_iff

alias ⟨_, StrictMonoOn.dual⟩ := strictMonoOn_dual_iff

alias ⟨_, StrictAntiOn.dual⟩ := strictAntiOn_dual_iff

end OrderDual

section WellFounded

variable [Preorder α] [Preorder β] {f : α → β}

@[to_dual]
/-
**StrictMono.wellFoundedLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.wellFoundedLT [WellFoundedLT β] (hf : StrictMono f) : WellFound
edLT α
参数：hf : StrictMono f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subrelation.isWellFounded`：Subrelation.isWellFounded (r : α -> α -> Prop
) [IsWellFounded α r] {s : α -> α -> Prop} (h : Subrelation s r) : IsWellFounded
 α s
· 使用定理 `instIsWellFoundedInvImage`：∀ {α : Type u} {β : Type v} (r : α → α → Prop
) [IsWellFounded α r] (f : β → α), IsWellFounded β (InvImage r f)
· 使用定理 `StrictMono.imp`：StrictMono.imp (hf : StrictMono f) (h : a < b) : f a < f
 b
-/
theorem StrictMono.wellFoundedLT [WellFoundedLT β] (hf : StrictMono f) : WellFoundedLT α :=
  Subrelation.isWellFounded (InvImage (· < ·) f) hf.imp

@[to_dual]
/-
**StrictAnti.wellFoundedLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAnti.wellFoundedLT [WellFoundedGT β] (hf : StrictAnti f) : WellFound
edLT α
参数：hf : StrictAnti f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subrelation.isWellFounded`：Subrelation.isWellFounded (r : α -> α -> Prop
) [IsWellFounded α r] {s : α -> α -> Prop} (h : Subrelation s r) : IsWellFounded
 α s
· 使用定理 `instIsWellFoundedInvImage`：∀ {α : Type u} {β : Type v} (r : α → α → Prop
) [IsWellFounded α r] (f : β → α), IsWellFounded β (InvImage r f)
· 使用定理 `StrictAnti.imp`：StrictAnti.imp (hf : StrictAnti f) (h : a < b) : f b < f
 a
-/
theorem StrictAnti.wellFoundedLT [WellFoundedGT β] (hf : StrictAnti f) : WellFoundedLT α :=
  Subrelation.isWellFounded (InvImage (· > ·) f) hf.imp

end WellFounded

/-! ### Miscellaneous monotonicity results -/

section PreorderPartialOrder

variable [Preorder α] [PartialOrder β] {f : α → β} {s : Set α}

/-
**MonotoneOn.strictMonoOn_of_injOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.strictMonoOn_of_injOn (hmono : MonotoneOn f s) (hinj : s.InjOn 
f) : StrictMonoOn f s
参数：hmono : MonotoneOn f s；hinj : s.InjOn f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
theorem MonotoneOn.strictMonoOn_of_injOn (hmono : MonotoneOn f s) (hinj : s.InjOn f) :
    StrictMonoOn f s :=
  fun _ hx _ hy h ↦ hmono hx hy h.le |>.lt_of_ne <| mt (hinj hx hy) h.ne
/-
**AntitoneOn.strictAntiOn_of_injOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.strictAntiOn_of_injOn (hanti : AntitoneOn f s) (hinj : s.InjOn 
f) : StrictAntiOn f s
参数：hanti : AntitoneOn f s；hinj : s.InjOn f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
theorem AntitoneOn.strictAntiOn_of_injOn (hanti : AntitoneOn f s) (hinj : s.InjOn f) :
    StrictAntiOn f s :=
  fun _ hx _ hy h ↦ hanti hx hy h.le |>.lt_of_ne' <| mt (hinj hx hy) h.ne

end PreorderPartialOrder

section Preorder

variable [Preorder α] [Preorder β] {f g : α → β} {a : α}

@[to_dual]
/-
**StrictMono.isMax_of_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.isMax_of_apply (hf : StrictMono f) (ha : IsMax (f a)) : IsMax a
参数：hf : StrictMono f；ha : IsMax (f a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_isMax_iff`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, ¬IsMax a ↔ 
∃ b, a < b
· 使用定理 `LT.lt.not_isMax`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b →
 ¬IsMax a
-/
theorem StrictMono.isMax_of_apply (hf : StrictMono f) (ha : IsMax (f a)) : IsMax a :=
  of_not_not fun h ↦
    let ⟨_, hb⟩ := not_isMax_iff.1 h
    (hf hb).not_isMax ha

@[to_dual]
/-
**StrictAnti.isMax_of_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAnti.isMax_of_apply (hf : StrictAnti f) (ha : IsMin (f a)) : IsMax a
参数：hf : StrictAnti f；ha : IsMin (f a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_isMax_iff`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, ¬IsMax a ↔ 
∃ b, a < b
· 使用定理 `LT.lt.not_isMin`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a →
 ¬IsMin a
-/
theorem StrictAnti.isMax_of_apply (hf : StrictAnti f) (ha : IsMin (f a)) : IsMax a :=
  of_not_not fun h ↦
    let ⟨_, hb⟩ := not_isMax_iff.1 h
    (hf hb).not_isMin ha
/-
**StrictMono.add_le_nat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.add_le_nat {f : Nat -> Nat} (hf : StrictMono f) (m n : Nat) : m
 + f n <= f (m + n)
参数：hf : StrictMono f；m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Nat.add_zero`：∀ (n : ℕ), n + 0 = n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_assoc`：∀ (n m k : ℕ), n + m + k = n + (m + k)
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
lemma StrictMono.add_le_nat {f : ℕ → ℕ} (hf : StrictMono f) (m n : ℕ) : m + f n ≤ f (m + n) := by
  rw [Nat.add_comm m, Nat.add_comm m]
  induction m with
  | zero => rw [Nat.add_zero, Nat.add_zero]
  | succ m ih =>
    rw [← Nat.add_assoc, ← Nat.add_assoc, Nat.succ_le_iff]
    exact ih.trans_lt (hf (n + m).lt_succ_self)
/-
**StrictMono.ite'** 是 Mathlib 中的一个定理，位于命名空间 `StrictMono`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : Preorder β] {f g
 : α → β},   StrictMono f →     StrictMono g →       ∀ {p : α → Prop} [inst_2 : 
DecidablePred p],         (∀ ⦃x y : α⦄, x < y → p y → p x) →           (∀ ⦃x y :
 α⦄, p x → ¬p y → x < y → f x < g y) → StrictMono fun x => if p x then f x else 
g x
参数：∀ ⦃x y : α⦄, x < y → p y → p x；∀ ⦃x y : α⦄, p x → ¬p y → x < y → f x < g y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
protected theorem StrictMono.ite' (hf : StrictMono f) (hg : StrictMono g) {p : α → Prop}
    [DecidablePred p]
    (hp : ∀ ⦃x y⦄, x < y → p y → p x) (hfg : ∀ ⦃x y⦄, p x → ¬p y → x < y → f x < g y) :
    StrictMono fun x ↦ if p x then f x else g x := by
  intro x y h
  by_cases hy : p y
  · have hx : p x := hp h hy
    simpa [hx, hy] using hf h
  by_cases hx : p x
  · simpa [hx, hy] using hfg hx hy h
  · simpa [hx, hy] using hg h
/-
**StrictMono.ite** 是 Mathlib 中的一个定理，位于命名空间 `StrictMono`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : Preorder β] {f g
 : α → β},   StrictMono f →     StrictMono g →       ∀ {p : α → Prop} [inst_2 : 
DecidablePred p],         (∀ ⦃x y : α⦄, x < y → p y → p x) → (∀ (x : α), f x ≤ g
 x) → StrictMono fun x => if p x then f x else g x
参数：∀ ⦃x y : α⦄, x < y → p y → p x；∀ (x : α), f x ≤ g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.ite'`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f g : α → β},   StrictMono f →     StrictMono g →       ∀ {p : α
 → Pr…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
protected theorem StrictMono.ite (hf : StrictMono f) (hg : StrictMono g) {p : α → Prop}
    [DecidablePred p] (hp : ∀ ⦃x y⦄, x < y → p y → p x) (hfg : ∀ x, f x ≤ g x) :
    StrictMono fun x ↦ if p x then f x else g x :=
  (hf.ite' hg hp) fun _ y _ _ h ↦ (hf h).trans_le (hfg y)
/-
**StrictAnti.ite'** 是 Mathlib 中的一个定理，位于命名空间 `StrictAnti`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : Preorder β] {f g
 : α → β},   StrictAnti f →     StrictAnti g →       ∀ {p : α → Prop} [inst_2 : 
DecidablePred p],         (∀ ⦃x y : α⦄, x < y → p y → p x) →           (∀ ⦃x y :
 α⦄, p x → ¬p y → x < y → g y < f x) → StrictAnti fun x => if p x then f x else 
g x
参数：∀ ⦃x y : α⦄, x < y → p y → p x；∀ ⦃x y : α⦄, p x → ¬p y → x < y → g y < f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.ite'`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f g : α → β},   StrictMono f →     StrictMono g →       ∀ {p : α
 → Pr…
· 使用定理 `StrictAnti.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β},   StrictAnti f → StrictMono (⇑OrderDual.toDual
 ∘ f)
-/
protected theorem StrictAnti.ite' (hf : StrictAnti f) (hg : StrictAnti g) {p : α → Prop}
    [DecidablePred p]
    (hp : ∀ ⦃x y⦄, x < y → p y → p x) (hfg : ∀ ⦃x y⦄, p x → ¬p y → x < y → g y < f x) :
    StrictAnti fun x ↦ if p x then f x else g x :=
  StrictMono.ite' hf.dual_right hg.dual_right hp hfg
/-
**StrictAnti.ite** 是 Mathlib 中的一个定理，位于命名空间 `StrictAnti`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : Preorder β] {f g
 : α → β},   StrictAnti f →     StrictAnti g →       ∀ {p : α → Prop} [inst_2 : 
DecidablePred p],         (∀ ⦃x y : α⦄, x < y → p y → p x) → (∀ (x : α), g x ≤ f
 x) → StrictAnti fun x => if p x then f x else g x
参数：∀ ⦃x y : α⦄, x < y → p y → p x；∀ (x : α), g x ≤ f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.ite'`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f g : α → β},   StrictAnti f →     StrictAnti g →       ∀ {p : α
 → Pr…
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
-/
protected theorem StrictAnti.ite (hf : StrictAnti f) (hg : StrictAnti g) {p : α → Prop}
    [DecidablePred p] (hp : ∀ ⦃x y⦄, x < y → p y → p x) (hfg : ∀ x, g x ≤ f x) :
    StrictAnti fun x ↦ if p x then f x else g x :=
  (hf.ite' hg hp) fun _ y _ _ h ↦ (hfg y).trans_lt (hf h)

end Preorder

namespace List

section Fold

/-
**List.foldl_monotone** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：foldl_monotone [Preorder α] {f : α -> β -> α} (H : forall b, Monotone fun 
a => f a b) (l : List β) : Monotone fun a => l.foldl f a
参数：H : forall b, Monotone fun a => f a b；l : List β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem foldl_monotone [Preorder α] {f : α → β → α} (H : ∀ b, Monotone fun a ↦ f a b)
    (l : List β) : Monotone fun a ↦ l.foldl f a :=
  List.recOn l (fun _ _ ↦ id) fun _ _ hl _ _ h ↦ hl (H _ h)
/-
**List.foldr_monotone** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：foldr_monotone [Preorder β] {f : α -> β -> β} (H : forall a, Monotone (f a
)) (l : List α) : Monotone fun b => l.foldr f b
参数：H : forall a, Monotone (f a)；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem foldr_monotone [Preorder β] {f : α → β → β} (H : ∀ a, Monotone (f a)) (l : List α) :
    Monotone fun b ↦ l.foldr f b := fun _ _ h ↦ List.recOn l h fun i _ hl ↦ H i hl
/-
**List.foldl_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：foldl_strictMono [Preorder α] {f : α -> β -> α} (H : forall b, StrictMono 
fun a => f a b) (l : List β) : StrictMono fun a => l.foldl f a
参数：H : forall b, StrictMono fun a => f a b；l : List β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem foldl_strictMono [Preorder α] {f : α → β → α} (H : ∀ b, StrictMono fun a ↦ f a b)
    (l : List β) : StrictMono fun a ↦ l.foldl f a :=
  List.recOn l (fun _ _ ↦ id) fun _ _ hl _ _ h ↦ hl (H _ h)
/-
**List.foldr_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：foldr_strictMono [Preorder β] {f : α -> β -> β} (H : forall a, StrictMono 
(f a)) (l : List α) : StrictMono fun b => l.foldr f b
参数：H : forall a, StrictMono (f a)；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem foldr_strictMono [Preorder β] {f : α → β → β} (H : ∀ a, StrictMono (f a)) (l : List α) :
    StrictMono fun b ↦ l.foldr f b := fun _ _ h ↦ List.recOn l h fun i _ hl ↦ H i hl

end Fold

end List

/-! ### Monotonicity in linear orders  -/


section LinearOrder

variable [LinearOrder α]

section Preorder

variable [Preorder β] {f : α → β} {s : Set α}

open Ordering

@[to_dual self (reorder := a b, ha hb)]
/-
**StrictMonoOn.le_iff_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMonoOn.le_iff_le (hf : StrictMonoOn f s) {a b : α} (ha : a in s) (hb
 : b in s) : f a <= f b ↔ a <= b
参数：hf : StrictMonoOn f s；ha : a in s；hb : b in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LE.le.lt_or_eq_dec`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α} [
DecidableLE α], a ≤ b → a < b ∨ a = b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem StrictMonoOn.le_iff_le (hf : StrictMonoOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
    f a ≤ f b ↔ a ≤ b :=
  ⟨fun h ↦ le_of_not_gt fun h' ↦ (hf hb ha h').not_ge h, fun h ↦
    h.lt_or_eq_dec.elim (fun h' ↦ (hf ha hb h').le) fun h' ↦ h' ▸ le_rfl⟩

@[to_dual self (reorder := a b, ha hb)]
/-
**StrictAntiOn.le_iff_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAntiOn.le_iff_ge (hf : StrictAntiOn f s) {a b : α} (ha : a in s) (hb
 : b in s) : f a <= f b ↔ b <= a
参数：hf : StrictAntiOn f s；ha : a in s；hb : b in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.le_iff_le`：StrictMonoOn.le_iff_le (hf : StrictMonoOn f s) {
a b : α} (ha : a in s) (hb : b in s) : f a <= f b ↔ a <= b
· 使用定理 `StrictAntiOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β} {s : Set α},   StrictAntiOn f s → StrictMonoO
n (⇑OrderDual…
-/
theorem StrictAntiOn.le_iff_ge (hf : StrictAntiOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
    f a ≤ f b ↔ b ≤ a :=
  hf.dual_right.le_iff_le hb ha
/-
**StrictMonoOn.eq_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMonoOn.eq_iff_eq (hf : StrictMonoOn f s) {a b : α} (ha : a in s) (hb
 : b in s) : f a = f b ↔ a = b
参数：hf : StrictMonoOn f s；ha : a in s；hb : b in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `StrictMonoOn.le_iff_le`：StrictMonoOn.le_iff_le (hf : StrictMonoOn f s) {
a b : α} (ha : a in s) (hb : b in s) : f a <= f b ↔ a <= b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
theorem StrictMonoOn.eq_iff_eq (hf : StrictMonoOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
    f a = f b ↔ a = b :=
  ⟨fun h ↦ le_antisymm ((hf.le_iff_le ha hb).mp h.le) ((hf.le_iff_le hb ha).mp h.ge), by
    rintro rfl
    rfl⟩
/-
**StrictAntiOn.eq_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAntiOn.eq_iff_eq (hf : StrictAntiOn f s) {a b : α} (ha : a in s) (hb
 : b in s) : f a = f b ↔ b = a
参数：hf : StrictAntiOn f s；ha : a in s；hb : b in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `StrictMonoOn.eq_iff_eq`：StrictMonoOn.eq_iff_eq (hf : StrictMonoOn f s) {
a b : α} (ha : a in s) (hb : b in s) : f a = f b ↔ a = b
· 使用定理 `StrictAntiOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β} {s : Set α},   StrictAntiOn f s → StrictMonoO
n (⇑OrderDual…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
theorem StrictAntiOn.eq_iff_eq (hf : StrictAntiOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
    f a = f b ↔ b = a :=
  (hf.dual_right.eq_iff_eq ha hb).trans eq_comm

@[to_dual self (reorder := a b, ha hb)]
/-
**StrictMonoOn.lt_iff_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMonoOn.lt_iff_lt (hf : StrictMonoOn f s) {a b : α} (ha : a in s) (hb
 : b in s) : f a < f b ↔ a < b
参数：hf : StrictMonoOn f s；ha : a in s；hb : b in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `lt_iff_le_not_ge`：lt_iff_le_not_ge : a < b ↔ a <= b ∧ ¬b <= a
· 使用定理 `StrictMonoOn.le_iff_le`：StrictMonoOn.le_iff_le (hf : StrictMonoOn f s) {
a b : α} (ha : a in s) (hb : b in s) : f a <= f b ↔ a <= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem StrictMonoOn.lt_iff_lt (hf : StrictMonoOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
    f a < f b ↔ a < b := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge, hf.le_iff_le ha hb, hf.le_iff_le hb ha]

@[to_dual self (reorder := a b, ha hb)]
/-
**StrictAntiOn.lt_iff_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAntiOn.lt_iff_gt (hf : StrictAntiOn f s) {a b : α} (ha : a in s) (hb
 : b in s) : f a < f b ↔ b < a
参数：hf : StrictAntiOn f s；ha : a in s；hb : b in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.lt_iff_lt`：StrictMonoOn.lt_iff_lt (hf : StrictMonoOn f s) {
a b : α} (ha : a in s) (hb : b in s) : f a < f b ↔ a < b
· 使用定理 `StrictAntiOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β} {s : Set α},   StrictAntiOn f s → StrictMonoO
n (⇑OrderDual…
-/
theorem StrictAntiOn.lt_iff_gt (hf : StrictAntiOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
    f a < f b ↔ b < a :=
  hf.dual_right.lt_iff_lt hb ha

@[to_dual self]
/-
**StrictMono.le_iff_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.le_iff_le (hf : StrictMono f) {a b : α} : f a <= f b ↔ a <= b
参数：hf : StrictMono f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.le_iff_le`：StrictMonoOn.le_iff_le (hf : StrictMonoOn f s) {
a b : α} (ha : a in s) (hb : b in s) : f a <= f b ↔ a <= b
· 使用定理 `StrictMono.strictMonoOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictMono f → ∀ (s : Set α), StrictMonoOn
 f s
· 使用定理 `trivial`：True
-/
theorem StrictMono.le_iff_le (hf : StrictMono f) {a b : α} : f a ≤ f b ↔ a ≤ b :=
  (hf.strictMonoOn Set.univ).le_iff_le trivial trivial

@[to_dual self]
/-
**StrictAnti.le_iff_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAnti.le_iff_ge (hf : StrictAnti f) {a b : α} : f a <= f b ↔ b <= a
参数：hf : StrictAnti f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAntiOn.le_iff_ge`：StrictAntiOn.le_iff_ge (hf : StrictAntiOn f s) {
a b : α} (ha : a in s) (hb : b in s) : f a <= f b ↔ b <= a
· 使用定理 `StrictAnti.strictAntiOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictAnti f → ∀ (s : Set α), StrictAntiOn
 f s
· 使用定理 `trivial`：True
-/
theorem StrictAnti.le_iff_ge (hf : StrictAnti f) {a b : α} : f a ≤ f b ↔ b ≤ a :=
  (hf.strictAntiOn Set.univ).le_iff_ge trivial trivial

@[to_dual self]
/-
**StrictMono.lt_iff_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α} : f a < f b ↔ a < b
参数：hf : StrictMono f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.lt_iff_lt`：StrictMonoOn.lt_iff_lt (hf : StrictMonoOn f s) {
a b : α} (ha : a in s) (hb : b in s) : f a < f b ↔ a < b
· 使用定理 `StrictMono.strictMonoOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictMono f → ∀ (s : Set α), StrictMonoOn
 f s
· 使用定理 `trivial`：True
-/
theorem StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α} : f a < f b ↔ a < b :=
  (hf.strictMonoOn Set.univ).lt_iff_lt trivial trivial

@[to_dual self]
/-
**StrictAnti.lt_iff_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAnti.lt_iff_gt (hf : StrictAnti f) {a b : α} : f a < f b ↔ b < a
参数：hf : StrictAnti f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAntiOn.lt_iff_gt`：StrictAntiOn.lt_iff_gt (hf : StrictAntiOn f s) {
a b : α} (ha : a in s) (hb : b in s) : f a < f b ↔ b < a
· 使用定理 `StrictAnti.strictAntiOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictAnti f → ∀ (s : Set α), StrictAntiOn
 f s
· 使用定理 `trivial`：True
-/
theorem StrictAnti.lt_iff_gt (hf : StrictAnti f) {a b : α} : f a < f b ↔ b < a :=
  (hf.strictAntiOn Set.univ).lt_iff_gt trivial trivial
/-
**StrictMonoOn.compares** 是 Mathlib 中的一个定理，位于命名空间 `StrictMonoOn`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [inst_1 : Preorder β] {
f : α → β} {s : Set α},   StrictMonoOn f s → ∀ {a b : α}, a ∈ s → b ∈ s → ∀ {o :
 Ordering}, o.Compares (f a) (f b) ↔ o.Compares a b
参数：f a；f b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.lt_iff_lt`：StrictMonoOn.lt_iff_lt (hf : StrictMonoOn f s) {
a b : α} (ha : a in s) (hb : b in s) : f a < f b ↔ a < b
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `StrictMonoOn.le_iff_le`：StrictMonoOn.le_iff_le (hf : StrictMonoOn f s) {
a b : α} (ha : a in s) (hb : b in s) : f a <= f b ↔ a <= b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
protected theorem StrictMonoOn.compares (hf : StrictMonoOn f s) {a b : α} (ha : a ∈ s)
    (hb : b ∈ s) : ∀ {o : Ordering}, o.Compares (f a) (f b) ↔ o.Compares a b
  | Ordering.lt => hf.lt_iff_lt ha hb
  | Ordering.eq => ⟨fun h ↦ ((hf.le_iff_le ha hb).1 h.le).antisymm
                      ((hf.le_iff_le hb ha).1 h.symm.le), congr_arg _⟩
  | Ordering.gt => hf.lt_iff_lt hb ha
/-
**StrictAntiOn.compares** 是 Mathlib 中的一个定理，位于命名空间 `StrictAntiOn`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [inst_1 : Preorder β] {
f : α → β} {s : Set α},   StrictAntiOn f s → ∀ {a b : α}, a ∈ s → b ∈ s → ∀ {o :
 Ordering}, o.Compares (f a) (f b) ↔ o.Compares b a
参数：f a；f b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `toDual_compares_toDual`：toDual_compares_toDual [LT α] {a b : α} {o : Ord
ering} : Compares o (toDual a) (toDual b) ↔ Compares o b a
· 使用定理 `StrictMonoOn.compares`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α
] [inst_1 : Preorder β] {f : α → β} {s : Set α},   StrictMonoOn f s → ∀ {a b : α
}, a ∈ s → …
· 使用定理 `StrictAntiOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β} {s : Set α},   StrictAntiOn f s → StrictMonoO
n (⇑OrderDual…
-/
protected theorem StrictAntiOn.compares (hf : StrictAntiOn f s) {a b : α} (ha : a ∈ s)
    (hb : b ∈ s) {o : Ordering} : o.Compares (f a) (f b) ↔ o.Compares b a :=
  toDual_compares_toDual.trans <| hf.dual_right.compares hb ha
/-
**StrictMono.compares** 是 Mathlib 中的一个定理，位于命名空间 `StrictMono`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [inst_1 : Preorder β] {
f : α → β},   StrictMono f → ∀ {a b : α} {o : Ordering}, o.Compares (f a) (f b) 
↔ o.Compares a b
参数：f a；f b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.compares`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α
] [inst_1 : Preorder β] {f : α → β} {s : Set α},   StrictMonoOn f s → ∀ {a b : α
}, a ∈ s → …
· 使用定理 `StrictMono.strictMonoOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictMono f → ∀ (s : Set α), StrictMonoOn
 f s
· 使用定理 `trivial`：True
-/
protected theorem StrictMono.compares (hf : StrictMono f) {a b : α} {o : Ordering} :
    o.Compares (f a) (f b) ↔ o.Compares a b :=
  (hf.strictMonoOn Set.univ).compares trivial trivial
/-
**StrictAnti.compares** 是 Mathlib 中的一个定理，位于命名空间 `StrictAnti`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [inst_1 : Preorder β] {
f : α → β},   StrictAnti f → ∀ {a b : α} {o : Ordering}, o.Compares (f a) (f b) 
↔ o.Compares b a
参数：f a；f b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAntiOn.compares`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α
] [inst_1 : Preorder β] {f : α → β} {s : Set α},   StrictAntiOn f s → ∀ {a b : α
}, a ∈ s → …
· 使用定理 `StrictAnti.strictAntiOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictAnti f → ∀ (s : Set α), StrictAntiOn
 f s
· 使用定理 `trivial`：True
-/
protected theorem StrictAnti.compares (hf : StrictAnti f) {a b : α} {o : Ordering} :
    o.Compares (f a) (f b) ↔ o.Compares b a :=
  (hf.strictAntiOn Set.univ).compares trivial trivial
/-
**StrictMono.injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.injective (hf : StrictMono f) : Injective f
参数：hf : StrictMono f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `StrictMono.compares`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] 
[inst_1 : Preorder β] {f : α → β},   StrictMono f → ∀ {a b : α} {o : Ordering}, 
o.Compare…
-/
theorem StrictMono.injective (hf : StrictMono f) : Injective f :=
  fun x y h ↦ show Compares eq x y from hf.compares.1 h
/-
**StrictAnti.injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAnti.injective (hf : StrictAnti f) : Injective f
参数：hf : StrictAnti f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `StrictAnti.compares`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] 
[inst_1 : Preorder β] {f : α → β},   StrictAnti f → ∀ {a b : α} {o : Ordering}, 
o.Compare…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem StrictAnti.injective (hf : StrictAnti f) : Injective f :=
  fun x y h ↦ show Compares eq x y from hf.compares.1 h.symm
/-
**StrictMonoOn.injOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMonoOn.injOn (hf : StrictMonoOn f s) : s.InjOn f
参数：hf : StrictMonoOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `StrictMonoOn.compares`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α
] [inst_1 : Preorder β] {f : α → β} {s : Set α},   StrictMonoOn f s → ∀ {a b : α
}, a ∈ s → …
-/
lemma StrictMonoOn.injOn (hf : StrictMonoOn f s) : s.InjOn f := fun x hx y hy hxy ↦
  show Ordering.eq.Compares x y from (hf.compares hx hy).1 hxy
/-
**StrictAntiOn.injOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAntiOn.injOn (hf : StrictAntiOn f s) : s.InjOn f
参数：hf : StrictAntiOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictMonoOn.injOn`：StrictMonoOn.injOn (hf : StrictMonoOn f s) : s.InjOn
 f
· 使用定理 `StrictAntiOn.dual_left`：∀ {α : Type u} {β : Type v} [inst : Preorder α] 
[inst_1 : Preorder β] {f : α → β} {s : Set α},   StrictAntiOn f s → StrictMonoOn
 (f ∘ ⇑Order…
-/
lemma StrictAntiOn.injOn (hf : StrictAntiOn f s) : s.InjOn f := hf.dual_left.injOn

@[to_dual]
/-
**StrictMono.maximal_of_maximal_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.maximal_of_maximal_image (hf : StrictMono f) {a} (hmax : forall
 p, p <= f a) (x : α) : x <= a
参数：hf : StrictMono f；hmax : forall p, p <= f a；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
-/
theorem StrictMono.maximal_of_maximal_image (hf : StrictMono f) {a} (hmax : ∀ p, p ≤ f a) (x : α) :
    x ≤ a :=
  hf.le_iff_le.mp (hmax (f x))

@[to_dual]
/-
**StrictAnti.minimal_of_maximal_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAnti.minimal_of_maximal_image (hf : StrictAnti f) {a} (hmax : forall
 p, p <= f a) (x : α) : a <= x
参数：hf : StrictAnti f；hmax : forall p, p <= f a；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `StrictAnti.le_iff_ge`：StrictAnti.le_iff_ge (hf : StrictAnti f) {a b : α}
 : f a <= f b ↔ b <= a
-/
theorem StrictAnti.minimal_of_maximal_image (hf : StrictAnti f) {a} (hmax : ∀ p, p ≤ f a) (x : α) :
    a ≤ x :=
  hf.le_iff_ge.mp (hmax (f x))

end Preorder

section PartialOrder

variable [PartialOrder β] {f : α → β} {s : Set α}

/-
**Monotone.strictMono_iff_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.strictMono_iff_injective (hf : Monotone f) : StrictMono f ↔ Injec
tive f
参数：hf : Monotone f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `Monotone.strictMono_of_injective`：Monotone.strictMono_of_injective (h₁ :
 Monotone f) (h₂ : Injective f) : StrictMono f
-/
theorem Monotone.strictMono_iff_injective (hf : Monotone f) : StrictMono f ↔ Injective f :=
  ⟨fun h ↦ h.injective, hf.strictMono_of_injective⟩
/-
**Antitone.strictAnti_iff_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.strictAnti_iff_injective (hf : Antitone f) : StrictAnti f ↔ Injec
tive f
参数：hf : Antitone f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.injective`：StrictAnti.injective (hf : StrictAnti f) : Injecti
ve f
· 使用定理 `Antitone.strictAnti_of_injective`：Antitone.strictAnti_of_injective (h₁ :
 Antitone f) (h₂ : Injective f) : StrictAnti f
-/
theorem Antitone.strictAnti_iff_injective (hf : Antitone f) : StrictAnti f ↔ Injective f :=
  ⟨fun h ↦ h.injective, hf.strictAnti_of_injective⟩
/-
**MonotoneOn.strictMonoOn_iff_injOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.strictMonoOn_iff_injOn (hf : MonotoneOn f s) : StrictMonoOn f s
 ↔ s.InjOn f
参数：hf : MonotoneOn f s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictMonoOn.injOn`：StrictMonoOn.injOn (hf : StrictMonoOn f s) : s.InjOn
 f
· 使用定理 `MonotoneOn.strictMonoOn_of_injOn`：MonotoneOn.strictMonoOn_of_injOn (hmon
o : MonotoneOn f s) (hinj : s.InjOn f) : StrictMonoOn f s
-/
theorem MonotoneOn.strictMonoOn_iff_injOn (hf : MonotoneOn f s) : StrictMonoOn f s ↔ s.InjOn f :=
  ⟨StrictMonoOn.injOn, hf.strictMonoOn_of_injOn⟩
/-
**AntitoneOn.strictAnti_iff_injOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.strictAnti_iff_injOn (hf : AntitoneOn f s) : StrictAntiOn f s ↔
 s.InjOn f
参数：hf : AntitoneOn f s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictAntiOn.injOn`：StrictAntiOn.injOn (hf : StrictAntiOn f s) : s.InjOn
 f
· 使用定理 `AntitoneOn.strictAntiOn_of_injOn`：AntitoneOn.strictAntiOn_of_injOn (hant
i : AntitoneOn f s) (hinj : s.InjOn f) : StrictAntiOn f s
-/
theorem AntitoneOn.strictAnti_iff_injOn (hf : AntitoneOn f s) : StrictAntiOn f s ↔ s.InjOn f :=
  ⟨StrictAntiOn.injOn, hf.strictAntiOn_of_injOn⟩

/-- If a monotone function is equal at two points, it is equal between all of them -/
/-
**Monotone.eq_of_ge_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.eq_of_ge_of_le {a₁ a₂ : α} (h_mon : Monotone f) (h_fa : f a₁ = f 
a₂) {i : α} (h₁ : a₁ <= i) (h₂ : i <= a₂) : f i = f a₁
参数：h_mon : Monotone f；h_fa : f a₁ = f a₂；h₁ : a₁ <= i；h₂ : i <= a₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
If a monotone function is equal at two points, it is equal between all of them
-/
theorem Monotone.eq_of_ge_of_le {a₁ a₂ : α} (h_mon : Monotone f) (h_fa : f a₁ = f a₂) {i : α}
    (h₁ : a₁ ≤ i) (h₂ : i ≤ a₂) : f i = f a₁ := by
  apply le_antisymm
  · rw [h_fa]; exact h_mon h₂
  · exact h_mon h₁

/-- If an antitone function is equal at two points, it is equal between all of them -/
/-
**Antitone.eq_of_ge_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.eq_of_ge_of_le {a₁ a₂ : α} (h_anti : Antitone f) (h_fa : f a₁ = f
 a₂) {i : α} (h₁ : a₁ <= i) (h₂ : i <= a₂) : f i = f a₁
参数：h_anti : Antitone f；h_fa : f a₁ = f a₂；h₁ : a₁ <= i；h₂ : i <= a₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
If an antitone function is equal at two points, it is equal between all of them
-/
theorem Antitone.eq_of_ge_of_le {a₁ a₂ : α} (h_anti : Antitone f) (h_fa : f a₁ = f a₂) {i : α}
    (h₁ : a₁ ≤ i) (h₂ : i ≤ a₂) : f i = f a₁ := by
  apply le_antisymm
  · exact h_anti h₁
  · rw [h_fa]; exact h_anti h₂

end PartialOrder

variable [LinearOrder β] {f : α → β} {s : Set α} {x y : α}

/-- A function between linear orders which is neither monotone nor antitone makes a dent upright or
downright. -/
/-
**not_monotone_not_antitone_iff_exists_le_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_monotone_not_antitone_iff_exists_le_le : ¬ Monotone f ∧ ¬ Antitone f ↔
 exists a b c, a <= b ∧ b <= c ∧ ((f a < f b ∧ f c < f b) ∨ (f b < f a ∧ f b < f
 c))
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function between linear orders which is neither monotone nor antitone makes a 
dent upright or
downright.
-/
lemma not_monotone_not_antitone_iff_exists_le_le :
    ¬ Monotone f ∧ ¬ Antitone f ↔
      ∃ a b c, a ≤ b ∧ b ≤ c ∧ ((f a < f b ∧ f c < f b) ∨ (f b < f a ∧ f b < f c)) := by
  simp only [Monotone, Antitone]
  grind [not_le]

/-- A function between linear orders which is neither monotone nor antitone makes a dent upright or
downright. -/
/-
**not_monotone_not_antitone_iff_exists_lt_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_monotone_not_antitone_iff_exists_lt_lt : ¬ Monotone f ∧ ¬ Antitone f ↔
 exists a b c, a < b ∧ b < c ∧ (f a < f b ∧ f c < f b ∨ f b < f a ∧ f b < f c)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists₃_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {p q : (a : α) → (b : β a) → γ a b → Prop},   (∀ (a : α) (b : β a) (c 
: γ…
· 使用定理 `and_congr_left`：∀ {c a b : Prop}, (c → (a ↔ b)) → (a ∧ c ↔ b ∧ c)
· 使用定理 `Iff.and`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Ne.le_iff_lt`：Ne.le_iff_lt (h : a != b) : a <= b ↔ a < b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False

--- 原说明 ---
A function between linear orders which is neither monotone nor antitone makes a 
dent upright or
downright.
-/
lemma not_monotone_not_antitone_iff_exists_lt_lt :
    ¬ Monotone f ∧ ¬ Antitone f ↔ ∃ a b c, a < b ∧ b < c ∧
    (f a < f b ∧ f c < f b ∨ f b < f a ∧ f b < f c) := by
  simp_rw [not_monotone_not_antitone_iff_exists_le_le, ← and_assoc]
  refine exists₃_congr (fun a b c ↦ and_congr_left <|
    fun h ↦ (Ne.le_iff_lt ?_).and <| Ne.le_iff_lt ?_) <;>
  (rintro rfl; simp at h)

/-!
### Strictly monotone functions and `cmp`
-/


/-
**StrictMonoOn.cmp_map_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMonoOn.cmp_map_eq (hf : StrictMonoOn f s) (hx : x in s) (hy : y in s
) : cmp (f x) (f y) = cmp x y
参数：hf : StrictMonoOn f s；hx : x in s；hy : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordering.Compares.cmp_eq`：Ordering.Compares.cmp_eq [LinearOrder α] {a b 
: α} {o : Ordering} (h : o.Compares a b) : cmp a b = o
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `StrictMonoOn.compares`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α
] [inst_1 : Preorder β] {f : α → β} {s : Set α},   StrictMonoOn f s → ∀ {a b : α
}, a ∈ s → …
· 使用定理 `cmp_compares`：cmp_compares [LinearOrder α] (a b : α) : (cmp a b).Compare
s a b

--- 原说明 ---
### Strictly monotone functions and `cmp`
-/
theorem StrictMonoOn.cmp_map_eq (hf : StrictMonoOn f s) (hx : x ∈ s) (hy : y ∈ s) :
    cmp (f x) (f y) = cmp x y :=
  ((hf.compares hx hy).2 (cmp_compares x y)).cmp_eq
/-
**StrictMono.cmp_map_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.cmp_map_eq (hf : StrictMono f) (x y : α) : cmp (f x) (f y) = cm
p x y
参数：hf : StrictMono f；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.cmp_map_eq`：StrictMonoOn.cmp_map_eq (hf : StrictMonoOn f s)
 (hx : x in s) (hy : y in s) : cmp (f x) (f y) = cmp x y
· 使用定理 `StrictMono.strictMonoOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictMono f → ∀ (s : Set α), StrictMonoOn
 f s
· 使用定理 `trivial`：True
-/
theorem StrictMono.cmp_map_eq (hf : StrictMono f) (x y : α) : cmp (f x) (f y) = cmp x y :=
  (hf.strictMonoOn Set.univ).cmp_map_eq trivial trivial
/-
**StrictAntiOn.cmp_map_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAntiOn.cmp_map_eq (hf : StrictAntiOn f s) (hx : x in s) (hy : y in s
) : cmp (f x) (f y) = cmp y x
参数：hf : StrictAntiOn f s；hx : x in s；hy : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.cmp_map_eq`：StrictMonoOn.cmp_map_eq (hf : StrictMonoOn f s)
 (hx : x in s) (hy : y in s) : cmp (f x) (f y) = cmp x y
· 使用定理 `StrictAntiOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β} {s : Set α},   StrictAntiOn f s → StrictMonoO
n (⇑OrderDual…
-/
theorem StrictAntiOn.cmp_map_eq (hf : StrictAntiOn f s) (hx : x ∈ s) (hy : y ∈ s) :
    cmp (f x) (f y) = cmp y x :=
  hf.dual_right.cmp_map_eq hy hx
/-
**StrictAnti.cmp_map_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAnti.cmp_map_eq (hf : StrictAnti f) (x y : α) : cmp (f x) (f y) = cm
p y x
参数：hf : StrictAnti f；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAntiOn.cmp_map_eq`：StrictAntiOn.cmp_map_eq (hf : StrictAntiOn f s)
 (hx : x in s) (hy : y in s) : cmp (f x) (f y) = cmp y x
· 使用定理 `StrictAnti.strictAntiOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictAnti f → ∀ (s : Set α), StrictAntiOn
 f s
· 使用定理 `trivial`：True
-/
theorem StrictAnti.cmp_map_eq (hf : StrictAnti f) (x y : α) : cmp (f x) (f y) = cmp y x :=
  (hf.strictAntiOn Set.univ).cmp_map_eq trivial trivial

end LinearOrder

/-! ### Monotonicity in `ℕ` and `ℤ` -/


section Preorder

variable [Preorder α]

/-
**Nat.rel_of_forall_rel_succ_of_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.rel_of_forall_rel_succ_of_le_of_lt (r : β -> β -> Prop) [IsTrans β r] 
{f : Nat -> β} {a : Nat} (h : forall n, a <= n -> r (f n) (f (n + 1))) ⦃b c : Na
t⦄ (hab : a <= b) (hbc : b < c) : r (f b) (f c)
参数：r : β -> β -> Prop；h : forall n, a <= n -> r (f n) (f (n + 1))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
-/
theorem Nat.rel_of_forall_rel_succ_of_le_of_lt (r : β → β → Prop) [IsTrans β r] {f : ℕ → β} {a : ℕ}
    (h : ∀ n, a ≤ n → r (f n) (f (n + 1))) ⦃b c : ℕ⦄ (hab : a ≤ b) (hbc : b < c) :
    r (f b) (f c) := by
  induction hbc with
  | refl => exact h _ hab
  | step b_lt_k r_b_k => exact _root_.trans r_b_k (h _ (hab.trans_lt b_lt_k).le)
/-
**Nat.rel_of_forall_rel_succ_of_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.rel_of_forall_rel_succ_of_le_of_le (r : β -> β -> Prop) [Std.Refl r] [
IsTrans β r] {f : Nat -> β} {a : Nat} (h : forall n, a <= n -> r (f n) (f (n + 1
))) ⦃b c : Nat⦄ (hab : a <= b) (hbc : b <= c) : r (f b) (f c)
参数：r : β -> β -> Prop；h : forall n, a <= n -> r (f n) (f (n + 1))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `Nat.rel_of_forall_rel_succ_of_le_of_lt`：Nat.rel_of_forall_rel_succ_of_le
_of_lt (r : β -> β -> Prop) [IsTrans β r] {f : Nat -> β} {a : Nat} (h : forall n
, a <= n -> r (f n) (f (n + …
-/
theorem Nat.rel_of_forall_rel_succ_of_le_of_le (r : β → β → Prop) [Std.Refl r] [IsTrans β r]
    {f : ℕ → β} {a : ℕ} (h : ∀ n, a ≤ n → r (f n) (f (n + 1)))
    ⦃b c : ℕ⦄ (hab : a ≤ b) (hbc : b ≤ c) : r (f b) (f c) :=
  hbc.eq_or_lt.elim (fun h ↦ h ▸ refl _) (Nat.rel_of_forall_rel_succ_of_le_of_lt r h hab)
/-
**Nat.rel_of_forall_rel_succ_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.rel_of_forall_rel_succ_of_lt (r : β -> β -> Prop) [IsTrans β r] {f : N
at -> β} (h : forall n, r (f n) (f (n + 1))) ⦃a b : Nat⦄ (hab : a < b) : r (f a)
 (f b)
参数：r : β -> β -> Prop；h : forall n, r (f n) (f (n + 1))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.rel_of_forall_rel_succ_of_le_of_lt`：Nat.rel_of_forall_rel_succ_of_le
_of_lt (r : β -> β -> Prop) [IsTrans β r] {f : Nat -> β} {a : Nat} (h : forall n
, a <= n -> r (f n) (f (n + …
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Nat.rel_of_forall_rel_succ_of_lt (r : β → β → Prop) [IsTrans β r] {f : ℕ → β}
    (h : ∀ n, r (f n) (f (n + 1))) ⦃a b : ℕ⦄ (hab : a < b) : r (f a) (f b) :=
  Nat.rel_of_forall_rel_succ_of_le_of_lt r (fun n _ ↦ h n) le_rfl hab
/-
**Nat.rel_of_forall_rel_succ_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.rel_of_forall_rel_succ_of_le (r : β -> β -> Prop) [Std.Refl r] [IsTran
s β r] {f : Nat -> β} (h : forall n, r (f n) (f (n + 1))) ⦃a b : Nat⦄ (hab : a <
= b) : r (f a) (f b)
参数：r : β -> β -> Prop；h : forall n, r (f n) (f (n + 1))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.rel_of_forall_rel_succ_of_le_of_le`：Nat.rel_of_forall_rel_succ_of_le
_of_le (r : β -> β -> Prop) [Std.Refl r] [IsTrans β r] {f : Nat -> β} {a : Nat} 
(h : forall n, a <= n -> r (…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Nat.rel_of_forall_rel_succ_of_le (r : β → β → Prop) [Std.Refl r] [IsTrans β r] {f : ℕ → β}
    (h : ∀ n, r (f n) (f (n + 1))) ⦃a b : ℕ⦄ (hab : a ≤ b) : r (f a) (f b) :=
  Nat.rel_of_forall_rel_succ_of_le_of_le r (fun n _ ↦ h n) le_rfl hab
/-
**monotone_nat_of_le_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_nat_of_le_succ {f : Nat -> α} (hf : forall n, f n <= f (n + 1)) :
 Monotone f
参数：hf : forall n, f n <= f (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.rel_of_forall_rel_succ_of_le`：Nat.rel_of_forall_rel_succ_of_le (r : 
β -> β -> Prop) [Std.Refl r] [IsTrans β r] {f : Nat -> β} (h : forall n, r (f n)
 (f (n + 1))) ⦃a b : N…
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
-/
theorem monotone_nat_of_le_succ {f : ℕ → α} (hf : ∀ n, f n ≤ f (n + 1)) : Monotone f :=
  Nat.rel_of_forall_rel_succ_of_le (· ≤ ·) hf
/-
**monotone_add_nat_of_le_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_add_nat_of_le_succ {f : Nat -> α} {k : Nat} (hf : forall n >= k, 
f n <= f (n + 1)) : Monotone (fun n => f (n + k))
参数：hf : forall n >= k, f n <= f (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.rel_of_forall_rel_succ_of_le_of_le`：Nat.rel_of_forall_rel_succ_of_le
_of_le (r : β -> β -> Prop) [Std.Refl r] [IsTrans β r] {f : Nat -> β} {a : Nat} 
(h : forall n, a <= n -> r (…
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.add_le_add_iff_right`：∀ {m k n : ℕ}, m + n ≤ k + n ↔ m ≤ k
-/
theorem monotone_add_nat_of_le_succ {f : ℕ → α} {k : ℕ} (hf : ∀ n ≥ k, f n ≤ f (n + 1)) :
    Monotone (fun n ↦ f (n + k)) :=
  fun _ _ hle ↦ Nat.rel_of_forall_rel_succ_of_le_of_le (· ≤ ·) hf
    (Nat.le_add_left k _) (Nat.add_le_add_iff_right.mpr hle)

-- TODO replace `{ x | k ≤ x }` with `Set.Ici k`
/-
**monotoneOn_nat_Ici_of_le_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotoneOn_nat_Ici_of_le_succ {f : Nat -> α} {k : Nat} (hf : forall n >= k
, f n <= f (n + 1)) : MonotoneOn f { x | k <= x }
参数：hf : forall n >= k, f n <= f (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.rel_of_forall_rel_succ_of_le_of_le`：Nat.rel_of_forall_rel_succ_of_le
_of_le (r : β -> β -> Prop) [Std.Refl r] [IsTrans β r] {f : Nat -> β} {a : Nat} 
(h : forall n, a <= n -> r (…
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
-/
theorem monotoneOn_nat_Ici_of_le_succ {f : ℕ → α} {k : ℕ} (hf : ∀ n ≥ k, f n ≤ f (n + 1)) :
    MonotoneOn f { x | k ≤ x } :=
  fun _ hab _ _ hle ↦ Nat.rel_of_forall_rel_succ_of_le_of_le (· ≤ ·) hf hab hle

-- TODO replace `{ x | k ≤ x }` with `Set.Ici k`
/-
**monotone_add_nat_iff_monotoneOn_nat_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_add_nat_iff_monotoneOn_nat_Ici {f : Nat -> α} {k : Nat} : Monoton
e (fun n => f (n + k)) ↔ MonotoneOn f { x | k <= x }
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Nat.sub_le_sub_iff_right`：∀ {k m n : ℕ}, k ≤ m → (n - k ≤ m - k ↔ n ≤ m)
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `Nat.add_le_add_iff_right`：∀ {m k n : ℕ}, m + n ≤ k + n ↔ m ≤ k
-/
theorem monotone_add_nat_iff_monotoneOn_nat_Ici {f : ℕ → α} {k : ℕ} :
    Monotone (fun n ↦ f (n + k)) ↔ MonotoneOn f { x | k ≤ x } := by
  refine ⟨fun h x hx y hy hle ↦ ?_, fun h x y hle ↦ ?_⟩
  · rw [← Nat.sub_add_cancel hx, ← Nat.sub_add_cancel hy]
    rw [← Nat.sub_le_sub_iff_right hy] at hle
    exact h hle
  · rw [← Nat.add_le_add_iff_right] at hle
    exact h (Nat.le_add_left k x) (Nat.le_add_left k y) hle
/-
**antitone_nat_of_succ_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitone_nat_of_succ_le {f : Nat -> α} (hf : forall n, f (n + 1) <= f n) :
 Antitone f
参数：hf : forall n, f (n + 1) <= f n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
-/
theorem antitone_nat_of_succ_le {f : ℕ → α} (hf : ∀ n, f (n + 1) ≤ f n) : Antitone f :=
  @monotone_nat_of_le_succ αᵒᵈ _ _ hf
/-
**antitone_add_nat_of_succ_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitone_add_nat_of_succ_le {f : Nat -> α} {k : Nat} (hf : forall n >= k, 
f (n + 1) <= f n) : Antitone (fun n => f (n + k))
参数：hf : forall n >= k, f (n + 1) <= f n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `monotone_add_nat_of_le_succ`：monotone_add_nat_of_le_succ {f : Nat -> α} 
{k : Nat} (hf : forall n >= k, f n <= f (n + 1)) : Monotone (fun n => f (n + k))
-/
theorem antitone_add_nat_of_succ_le {f : ℕ → α} {k : ℕ} (hf : ∀ n ≥ k, f (n + 1) ≤ f n) :
    Antitone (fun n ↦ f (n + k)) :=
  @monotone_add_nat_of_le_succ αᵒᵈ _ f k hf

-- TODO replace `{ x | k ≤ x }` with `Set.Ici k`
/-
**antitoneOn_nat_Ici_of_succ_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitoneOn_nat_Ici_of_succ_le {f : Nat -> α} {k : Nat} (hf : forall n >= k
, f (n + 1) <= f n) : AntitoneOn f { x | k <= x }
参数：hf : forall n >= k, f (n + 1) <= f n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `monotoneOn_nat_Ici_of_le_succ`：monotoneOn_nat_Ici_of_le_succ {f : Nat ->
 α} {k : Nat} (hf : forall n >= k, f n <= f (n + 1)) : MonotoneOn f { x | k <= x
 }
-/
theorem antitoneOn_nat_Ici_of_succ_le {f : ℕ → α} {k : ℕ} (hf : ∀ n ≥ k, f (n + 1) ≤ f n) :
    AntitoneOn f { x | k ≤ x } :=
  @monotoneOn_nat_Ici_of_le_succ αᵒᵈ _ f k hf

-- TODO replace `{ x | k ≤ x }` with `Set.Ici k`
/-
**antitone_add_nat_iff_antitoneOn_nat_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitone_add_nat_iff_antitoneOn_nat_Ici {f : Nat -> α} {k : Nat} : Antiton
e (fun n => f (n + k)) ↔ AntitoneOn f { x | k <= x }
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `monotone_add_nat_iff_monotoneOn_nat_Ici`：monotone_add_nat_iff_monotoneOn
_nat_Ici {f : Nat -> α} {k : Nat} : Monotone (fun n => f (n + k)) ↔ MonotoneOn f
 { x | k <= x }
-/
theorem antitone_add_nat_iff_antitoneOn_nat_Ici {f : ℕ → α} {k : ℕ} :
    Antitone (fun n ↦ f (n + k)) ↔ AntitoneOn f { x | k ≤ x } :=
  @monotone_add_nat_iff_monotoneOn_nat_Ici αᵒᵈ _ f k
/-
**strictMono_nat_of_lt_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictMono_nat_of_lt_succ {f : Nat -> α} (hf : forall n, f n < f (n + 1)) 
: StrictMono f
参数：hf : forall n, f n < f (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.rel_of_forall_rel_succ_of_lt`：Nat.rel_of_forall_rel_succ_of_lt (r : 
β -> β -> Prop) [IsTrans β r] {f : Nat -> β} (h : forall n, r (f n) (f (n + 1)))
 ⦃a b : Nat⦄ (hab : a …
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
-/
theorem strictMono_nat_of_lt_succ {f : ℕ → α} (hf : ∀ n, f n < f (n + 1)) : StrictMono f :=
  Nat.rel_of_forall_rel_succ_of_lt (· < ·) hf
/-
**strictAnti_nat_of_succ_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictAnti_nat_of_succ_lt {f : Nat -> α} (hf : forall n, f (n + 1) < f n) 
: StrictAnti f
参数：hf : forall n, f (n + 1) < f n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictMono_nat_of_lt_succ`：strictMono_nat_of_lt_succ {f : Nat -> α} (hf 
: forall n, f n < f (n + 1)) : StrictMono f
-/
theorem strictAnti_nat_of_succ_lt {f : ℕ → α} (hf : ∀ n, f (n + 1) < f n) : StrictAnti f :=
  @strictMono_nat_of_lt_succ αᵒᵈ _ f hf

namespace Nat

/-- If `α` is a preorder with no maximal elements, then there exists a strictly monotone function
`ℕ → α` with any prescribed value of `f 0`. -/
/-
**Nat.exists_strictMono'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：exists_strictMono' [NoMaxOrder α] (a : α) : exists f : Nat -> α, StrictMon
o f ∧ f 0 = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictMono_nat_of_lt_succ`：strictMono_nat_of_lt_succ {f : Nat -> α} (hf 
: forall n, f n < f (n + 1)) : StrictMono f
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If `α` is a preorder with no maximal elements, then there exists a strictly mono
tone function
`ℕ → α` with any prescribed value of `f 0`.
-/
theorem exists_strictMono' [NoMaxOrder α] (a : α) : ∃ f : ℕ → α, StrictMono f ∧ f 0 = a := by
  choose g hg using fun x : α ↦ exists_gt x
  exact ⟨fun n ↦ Nat.recOn n a fun _ ↦ g, strictMono_nat_of_lt_succ fun n ↦ hg _, rfl⟩

/-- If `α` is a preorder with no maximal elements, then there exists a strictly antitone function
`ℕ → α` with any prescribed value of `f 0`. -/
/-
**Nat.exists_strictAnti'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：exists_strictAnti' [NoMinOrder α] (a : α) : exists f : Nat -> α, StrictAnt
i f ∧ f 0 = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_strictMono'`：exists_strictMono' [NoMaxOrder α] (a : α) : exis
ts f : Nat -> α, StrictMono f ∧ f 0 = a
· 使用定理 `OrderDual.noMaxOrder`：∀ {α : Type u_1} [inst : LT α] [NoMinOrder α], NoM
axOrder αᵒᵈ

--- 原说明 ---
If `α` is a preorder with no maximal elements, then there exists a strictly anti
tone function
`ℕ → α` with any prescribed value of `f 0`.
-/
theorem exists_strictAnti' [NoMinOrder α] (a : α) : ∃ f : ℕ → α, StrictAnti f ∧ f 0 = a :=
  exists_strictMono' (OrderDual.toDual a)
/-
**Nat.exists_strictMono_subsequence** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：exists_strictMono_subsequence {P : Nat -> Prop} (h : forall N, exists n > 
N, P n) : exists φ : Nat -> Nat, StrictMono φ ∧ forall n, P (φ n)
参数：h : forall N, exists n > N, P n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.exists_strictMono'`：exists_strictMono' [NoMaxOrder α] (a : α) : exis
ts f : Nat -> α, StrictMono f ∧ f 0 = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem exists_strictMono_subsequence {P : ℕ → Prop} (h : ∀ N, ∃ n > N, P n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P (φ n) := by
  have : NoMaxOrder {n // P n} :=
    ⟨fun n ↦ Exists.intro ⟨(h n.1).choose, (h n.1).choose_spec.2⟩ (h n.1).choose_spec.1⟩
  obtain ⟨f, hf, _⟩ := Nat.exists_strictMono' (⟨(h 0).choose, (h 0).choose_spec.2⟩ : {n // P n})
  exact Exists.intro (fun n ↦ (f n).1) ⟨hf, fun n ↦ (f n).2⟩

variable (α)

/-- If `α` is a nonempty preorder with no maximal elements, then there exists a strictly monotone
function `ℕ → α`. -/
/-
**Nat.exists_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：exists_strictMono [Nonempty α] [NoMaxOrder α] : exists f : Nat -> α, Stric
tMono f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_strictMono'`：exists_strictMono' [NoMaxOrder α] (a : α) : exis
ts f : Nat -> α, StrictMono f ∧ f 0 = a

--- 原说明 ---
If `α` is a nonempty preorder with no maximal elements, then there exists a stri
ctly monotone
function `ℕ → α`.
-/
theorem exists_strictMono [Nonempty α] [NoMaxOrder α] : ∃ f : ℕ → α, StrictMono f :=
  let ⟨a⟩ := ‹Nonempty α›
  let ⟨f, hf, _⟩ := exists_strictMono' a
  ⟨f, hf⟩

/-- If `α` is a nonempty preorder with no minimal elements, then there exists a strictly antitone
function `ℕ → α`. -/
/-
**Nat.exists_strictAnti** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：exists_strictAnti [Nonempty α] [NoMinOrder α] : exists f : Nat -> α, Stric
tAnti f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_strictMono`：exists_strictMono [Nonempty α] [NoMaxOrder α] : e
xists f : Nat -> α, StrictMono f
· 使用定理 `OrderDual.instNonempty`：∀ (α : Type u_2) [h : Nonempty α], Nonempty αᵒᵈ
· 使用定理 `OrderDual.noMaxOrder`：∀ {α : Type u_1} [inst : LT α] [NoMinOrder α], NoM
axOrder αᵒᵈ

--- 原说明 ---
If `α` is a nonempty preorder with no minimal elements, then there exists a stri
ctly antitone
function `ℕ → α`.
-/
theorem exists_strictAnti [Nonempty α] [NoMinOrder α] : ∃ f : ℕ → α, StrictAnti f :=
  exists_strictMono αᵒᵈ
/-
**Nat.pow_self_mono** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：pow_self_mono : Monotone fun n : Nat => n ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pow_succ`：∀ (n m : ℕ), n ^ m.succ = n ^ m * n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.pow_le_pow_left`：∀ {n m : ℕ}, n ≤ m → ∀ (i : ℕ), n ^ i ≤ m ^ i
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `Nat.le_mul_of_pos_right`：∀ {m : ℕ} (n : ℕ), 0 < m → n ≤ n * m
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
-/
lemma pow_self_mono : Monotone fun n : ℕ ↦ n ^ n := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  rw [Nat.pow_succ]
  exact (Nat.pow_le_pow_left n.le_succ _).trans (Nat.le_mul_of_pos_right _ n.succ_pos)
/-
**Nat.pow_monotoneOn** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：pow_monotoneOn : MonotoneOn (fun p : Nat × Nat => p.1 ^ p.2) {p | p.1 != 0
}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.pow_le_pow_left`：∀ {n m : ℕ}, n ≤ m → ∀ (i : ℕ), n ^ i ≤ m ^ i
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.pow_le_pow_right`：∀ {n : ℕ}, n > 0 → ∀ {i j : ℕ}, i ≤ j → n ^ i ≤ n 
^ j
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma pow_monotoneOn : MonotoneOn (fun p : ℕ × ℕ ↦ p.1 ^ p.2) {p | p.1 ≠ 0} := fun _p _ _q hq hpq ↦
  (Nat.pow_le_pow_left hpq.1 _).trans (Nat.pow_le_pow_right (Nat.pos_iff_ne_zero.2 hq) hpq.2)
/-
**Nat.pow_self_strictMonoOn** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：pow_self_strictMonoOn : StrictMonoOn (fun n : Nat => n ^ n) {n : Nat | n !
= 0}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.pow_lt_pow_left`：∀ {a b n : ℕ}, a < b → n ≠ 0 → a ^ n < b ^ n
· 使用定理 `Nat.pow_le_pow_right`：∀ {n : ℕ}, n > 0 → ∀ {i j : ℕ}, i ≤ j → n ^ i ≤ n 
^ j
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma pow_self_strictMonoOn : StrictMonoOn (fun n : ℕ ↦ n ^ n) {n : ℕ | n ≠ 0} :=
  fun _m hm _n hn hmn ↦
    (Nat.pow_lt_pow_left hmn hm).trans_le (Nat.pow_le_pow_right (Nat.pos_iff_ne_zero.2 hn) hmn.le)

end Nat

/-
**Int.rel_of_forall_rel_succ_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.rel_of_forall_rel_succ_of_lt (r : β -> β -> Prop) [IsTrans β r] {f : I
nt -> β} (h : forall n, r (f n) (f (n + 1))) ⦃a b : Int⦄ (hab : a < b) : r (f a)
 (f b)
参数：r : β -> β -> Prop；h : forall n, r (f n) (f (n + 1))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.lt.dest`：∀ {a b : ℤ}, a < b → ∃ n, a + ↑n.succ = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.ofNat_one`：↑1 = 1
· 使用定理 `Int.natCast_succ`：∀ (n : ℕ), ↑n.succ = ↑n + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.add_assoc`：∀ (a b c : ℤ), a + b + c = a + (b + c)
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
-/
theorem Int.rel_of_forall_rel_succ_of_lt (r : β → β → Prop) [IsTrans β r] {f : ℤ → β}
    (h : ∀ n, r (f n) (f (n + 1))) ⦃a b : ℤ⦄ (hab : a < b) : r (f a) (f b) := by
  rcases lt.dest hab with ⟨n, rfl⟩
  clear hab
  induction n with
  | zero => rw [Int.ofNat_one]; apply h
  | succ n ihn => rw [Int.natCast_succ, ← Int.add_assoc]; exact _root_.trans ihn (h _)
/-
**Int.rel_of_forall_rel_succ_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.rel_of_forall_rel_succ_of_le (r : β -> β -> Prop) [Std.Refl r] [IsTran
s β r] {f : Int -> β} (h : forall n, r (f n) (f (n + 1))) ⦃a b : Int⦄ (hab : a <
= b) : r (f a) (f b)
参数：r : β -> β -> Prop；h : forall n, r (f n) (f (n + 1))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `Int.rel_of_forall_rel_succ_of_lt`：Int.rel_of_forall_rel_succ_of_lt (r : 
β -> β -> Prop) [IsTrans β r] {f : Int -> β} (h : forall n, r (f n) (f (n + 1)))
 ⦃a b : Int⦄ (hab : a …
-/
theorem Int.rel_of_forall_rel_succ_of_le (r : β → β → Prop) [Std.Refl r] [IsTrans β r] {f : ℤ → β}
    (h : ∀ n, r (f n) (f (n + 1))) ⦃a b : ℤ⦄ (hab : a ≤ b) : r (f a) (f b) :=
  hab.eq_or_lt.elim (fun h ↦ h ▸ refl _) fun h' ↦ Int.rel_of_forall_rel_succ_of_lt r h h'
/-
**monotone_int_of_le_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_int_of_le_succ {f : Int -> α} (hf : forall n, f n <= f (n + 1)) :
 Monotone f
参数：hf : forall n, f n <= f (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.rel_of_forall_rel_succ_of_le`：Int.rel_of_forall_rel_succ_of_le (r : 
β -> β -> Prop) [Std.Refl r] [IsTrans β r] {f : Int -> β} (h : forall n, r (f n)
 (f (n + 1))) ⦃a b : I…
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
-/
theorem monotone_int_of_le_succ {f : ℤ → α} (hf : ∀ n, f n ≤ f (n + 1)) : Monotone f :=
  Int.rel_of_forall_rel_succ_of_le (· ≤ ·) hf
/-
**antitone_int_of_succ_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitone_int_of_succ_le {f : Int -> α} (hf : forall n, f (n + 1) <= f n) :
 Antitone f
参数：hf : forall n, f (n + 1) <= f n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.rel_of_forall_rel_succ_of_le`：Int.rel_of_forall_rel_succ_of_le (r : 
β -> β -> Prop) [Std.Refl r] [IsTrans β r] {f : Int -> β} (h : forall n, r (f n)
 (f (n + 1))) ⦃a b : I…
· 使用定理 `instReflGe`：∀ {α : Type u} [inst : Preorder α], Std.Refl fun x1 x2 => x2
 ≤ x1
· 使用定理 `instIsTransGe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x2 ≤ x1
-/
theorem antitone_int_of_succ_le {f : ℤ → α} (hf : ∀ n, f (n + 1) ≤ f n) : Antitone f :=
  Int.rel_of_forall_rel_succ_of_le (· ≥ ·) hf
/-
**strictMono_int_of_lt_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictMono_int_of_lt_succ {f : Int -> α} (hf : forall n, f n < f (n + 1)) 
: StrictMono f
参数：hf : forall n, f n < f (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.rel_of_forall_rel_succ_of_lt`：Int.rel_of_forall_rel_succ_of_lt (r : 
β -> β -> Prop) [IsTrans β r] {f : Int -> β} (h : forall n, r (f n) (f (n + 1)))
 ⦃a b : Int⦄ (hab : a …
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
-/
theorem strictMono_int_of_lt_succ {f : ℤ → α} (hf : ∀ n, f n < f (n + 1)) : StrictMono f :=
  Int.rel_of_forall_rel_succ_of_lt (· < ·) hf
/-
**strictAnti_int_of_succ_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictAnti_int_of_succ_lt {f : Int -> α} (hf : forall n, f (n + 1) < f n) 
: StrictAnti f
参数：hf : forall n, f (n + 1) < f n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.rel_of_forall_rel_succ_of_lt`：Int.rel_of_forall_rel_succ_of_lt (r : 
β -> β -> Prop) [IsTrans β r] {f : Int -> β} (h : forall n, r (f n) (f (n + 1)))
 ⦃a b : Int⦄ (hab : a …
· 使用定理 `instIsTransGt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x2 < x1
-/
theorem strictAnti_int_of_succ_lt {f : ℤ → α} (hf : ∀ n, f (n + 1) < f n) : StrictAnti f :=
  Int.rel_of_forall_rel_succ_of_lt (· > ·) hf

namespace Int

variable (α)
variable [Nonempty α] [NoMinOrder α] [NoMaxOrder α]

/-- If `α` is a nonempty preorder with no minimal or maximal elements, then there exists a strictly
monotone function `f : ℤ → α`. -/
/-
**Int.exists_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：exists_strictMono : exists f : Int -> α, StrictMono f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_strictMono'`：exists_strictMono' [NoMaxOrder α] (a : α) : exis
ts f : Nat -> α, StrictMono f ∧ f 0 = a
· 使用定理 `Nat.exists_strictAnti'`：exists_strictAnti' [NoMinOrder α] (a : α) : exis
ts f : Nat -> α, StrictAnti f ∧ f 0 = a
· 使用定理 `strictMono_int_of_lt_succ`：strictMono_int_of_lt_succ {f : Int -> α} (hf 
: forall n, f n < f (n + 1)) : StrictMono f
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.zero_lt_one`：0 < 1

--- 原说明 ---
If `α` is a nonempty preorder with no minimal or maximal elements, then there ex
ists a strictly
monotone function `f : ℤ → α`.
-/
theorem exists_strictMono : ∃ f : ℤ → α, StrictMono f := by
  inhabit α
  rcases Nat.exists_strictMono' (default : α) with ⟨f, hf, hf₀⟩
  rcases Nat.exists_strictAnti' (default : α) with ⟨g, hg, hg₀⟩
  refine ⟨fun n ↦ Int.casesOn n f fun n ↦ g (n + 1), strictMono_int_of_lt_succ ?_⟩
  rintro (n | _ | n)
  · exact hf n.lt_succ_self
  · change g 1 < f 0
    rw [hf₀, ← hg₀]
    exact hg Nat.zero_lt_one
  · exact hg (Nat.lt_succ_self _)

/-- If `α` is a nonempty preorder with no minimal or maximal elements, then there exists a strictly
antitone function `f : ℤ → α`. -/
/-
**Int.exists_strictAnti** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：exists_strictAnti : exists f : Int -> α, StrictAnti f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.exists_strictMono`：exists_strictMono : exists f : Int -> α, StrictMo
no f
· 使用定理 `OrderDual.instNonempty`：∀ (α : Type u_2) [h : Nonempty α], Nonempty αᵒᵈ
· 使用定理 `OrderDual.noMaxOrder`：∀ {α : Type u_1} [inst : LT α] [NoMinOrder α], NoM
axOrder αᵒᵈ

--- 原说明 ---
If `α` is a nonempty preorder with no minimal or maximal elements, then there ex
ists a strictly
antitone function `f : ℤ → α`.
-/
theorem exists_strictAnti : ∃ f : ℤ → α, StrictAnti f :=
  exists_strictMono αᵒᵈ

end Int

-- TODO@Yael: Generalize the following four to succ orders
/-- If `f` is a monotone function from `ℕ` to a preorder such that `x` lies between `f n` and
  `f (n + 1)`, then `x` doesn't lie in the range of `f`. -/
/-
**Monotone.ne_of_lt_of_lt_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.ne_of_lt_of_lt_nat {f : Nat -> α} (hf : Monotone f) (n : Nat) {x 
: α} (h1 : f n < x) (h2 : x < f (n + 1)) (a : Nat) : f a != x
参数：hf : Monotone f；n : Nat；h1 : f n < x；h2 : x < f (n + 1)；a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Monotone.reflect_lt`：Monotone.reflect_lt (hf : Monotone f) {a b : α} (h 
: f a < f b) : a < b
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n

--- 原说明 ---
If `f` is a monotone function from `ℕ` to a preorder such that `x` lies between 
`f n` and
  `f (n + 1)`, then `x` doesn't lie in the range of `f`.
-/
theorem Monotone.ne_of_lt_of_lt_nat {f : ℕ → α} (hf : Monotone f) (n : ℕ) {x : α} (h1 : f n < x)
    (h2 : x < f (n + 1)) (a : ℕ) : f a ≠ x := by
  rintro rfl
  exact (hf.reflect_lt h1).not_ge (Nat.le_of_lt_succ <| hf.reflect_lt h2)

/-- If `f` is an antitone function from `ℕ` to a preorder such that `x` lies between `f (n + 1)` and
`f n`, then `x` doesn't lie in the range of `f`. -/
/-
**Antitone.ne_of_lt_of_lt_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.ne_of_lt_of_lt_nat {f : Nat -> α} (hf : Antitone f) (n : Nat) {x 
: α} (h1 : f (n + 1) < x) (h2 : x < f n) (a : Nat) : f a != x
参数：hf : Antitone f；n : Nat；h1 : f (n + 1) < x；h2 : x < f n；a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Antitone.reflect_lt`：Antitone.reflect_lt (hf : Antitone f) {a b : α} (h 
: f a < f b) : b < a
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n

--- 原说明 ---
If `f` is an antitone function from `ℕ` to a preorder such that `x` lies between
 `f (n + 1)` and
`f n`, then `x` doesn't lie in the range of `f`.
-/
theorem Antitone.ne_of_lt_of_lt_nat {f : ℕ → α} (hf : Antitone f) (n : ℕ) {x : α}
    (h1 : f (n + 1) < x) (h2 : x < f n) (a : ℕ) : f a ≠ x := by
  rintro rfl
  exact (hf.reflect_lt h2).not_ge (Nat.le_of_lt_succ <| hf.reflect_lt h1)

/-- If `f` is a monotone function from `ℤ` to a preorder and `x` lies between `f n` and
  `f (n + 1)`, then `x` doesn't lie in the range of `f`. -/
/-
**Monotone.ne_of_lt_of_lt_int** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.ne_of_lt_of_lt_int {f : Int -> α} (hf : Monotone f) (n : Int) {x 
: α} (h1 : f n < x) (h2 : x < f (n + 1)) (a : Int) : f a != x
参数：hf : Monotone f；n : Int；h1 : f n < x；h2 : x < f (n + 1)；a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Monotone.reflect_lt`：Monotone.reflect_lt (hf : Monotone f) {a b : α} (h 
: f a < f b) : a < b
· 使用定理 `Int.le_of_lt_add_one`：∀ {a b : ℤ}, a < b + 1 → a ≤ b

--- 原说明 ---
If `f` is a monotone function from `ℤ` to a preorder and `x` lies between `f n` 
and
  `f (n + 1)`, then `x` doesn't lie in the range of `f`.
-/
theorem Monotone.ne_of_lt_of_lt_int {f : ℤ → α} (hf : Monotone f) (n : ℤ) {x : α} (h1 : f n < x)
    (h2 : x < f (n + 1)) (a : ℤ) : f a ≠ x := by
  rintro rfl
  exact (hf.reflect_lt h1).not_ge (Int.le_of_lt_add_one <| hf.reflect_lt h2)

/-- If `f` is an antitone function from `ℤ` to a preorder and `x` lies between `f (n + 1)` and
`f n`, then `x` doesn't lie in the range of `f`. -/
/-
**Antitone.ne_of_lt_of_lt_int** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.ne_of_lt_of_lt_int {f : Int -> α} (hf : Antitone f) (n : Int) {x 
: α} (h1 : f (n + 1) < x) (h2 : x < f n) (a : Int) : f a != x
参数：hf : Antitone f；n : Int；h1 : f (n + 1) < x；h2 : x < f n；a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Antitone.reflect_lt`：Antitone.reflect_lt (hf : Antitone f) {a b : α} (h 
: f a < f b) : b < a
· 使用定理 `Int.le_of_lt_add_one`：∀ {a b : ℤ}, a < b + 1 → a ≤ b

--- 原说明 ---
If `f` is an antitone function from `ℤ` to a preorder and `x` lies between `f (n
 + 1)` and
`f n`, then `x` doesn't lie in the range of `f`.
-/
theorem Antitone.ne_of_lt_of_lt_int {f : ℤ → α} (hf : Antitone f) (n : ℤ) {x : α}
    (h1 : f (n + 1) < x) (h2 : x < f n) (a : ℤ) : f a ≠ x := by
  rintro rfl
  exact (hf.reflect_lt h2).not_ge (Int.le_of_lt_add_one <| hf.reflect_lt h1)

end Preorder

/-- A monotone function `f : ℕ → ℕ` bounded by `b`, which is constant after stabilising for the
first time, stabilises in at most `b` steps. -/
/-
**Nat.stabilises_of_monotone** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.stabilises_of_monotone {f : Nat -> Nat} {b n : Nat} (hfmono : Monotone
 f) (hfb : forall m, f m <= b) (hfstab : forall m, f m = f (m + 1) -> f (m + 1) 
= f (m + 2)) (hbn : b <= n) : f n = f b
参数：hfmono : Monotone f；hfb : forall m, f m <= b；hfstab : forall m, f m = f (m + 
1) -> f (m + 1) = f (m + 2)；hbn : b <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `_private.Mathlib.Order.Monotone.Basic.0.Nat.stabilises_of_monotone.stric
tMono`：∀ {f : ℕ → ℕ} {b : ℕ}, Monotone f → (∀ m ≤ b, f m ≠ f (m + 1)) → ∀ m ≤ b 
+ 1, m ≤ f m
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Nat.add_sub_of_le`：∀ {a b : ℕ}, a ≤ b → a + (b - a) = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c

--- 原说明 ---
A monotone function `f : ℕ → ℕ` bounded by `b`, which is constant after stabilis
ing for the
first time, stabilises in at most `b` steps.
-/
lemma Nat.stabilises_of_monotone {f : ℕ → ℕ} {b n : ℕ} (hfmono : Monotone f) (hfb : ∀ m, f m ≤ b)
    (hfstab : ∀ m, f m = f (m + 1) → f (m + 1) = f (m + 2)) (hbn : b ≤ n) : f n = f b := by
  obtain ⟨m, hmb, hm⟩ : ∃ m ≤ b, f m = f (m + 1) := by
    contrapose! hfb
    let rec strictMono : ∀ m ≤ b + 1, m ≤ f m
    | 0, _ => Nat.zero_le _
    | m + 1, hmb => (strictMono _ <| m.le_succ.trans hmb).trans_lt <| (hfmono m.le_succ).lt_of_ne <|
        hfb _ <| Nat.le_of_succ_le_succ hmb
    exact ⟨b + 1, strictMono _ le_rfl⟩
  replace key : ∀ k : ℕ, f (m + k) = f (m + k + 1) ∧ f (m + k) = f m := fun k =>
    Nat.rec ⟨hm, rfl⟩ (fun k ih => ⟨hfstab _ ih.1, ih.1.symm.trans ih.2⟩) k
  replace key : ∀ k ≥ m, f k = f m := fun k hk =>
    (congr_arg f (Nat.add_sub_of_le hk)).symm.trans (key (k - m)).2
  exact (key n (hmb.trans hbn)).trans (key b hmb).symm

/-- An antitone function `f : ℕ → ℕ` which is constant after stabilising for the first time,
stabilises in at most `f 0` steps.

Compared to `WellFoundedLT.antitone_chain_condition`, this lemma requires the extra hypothesis
`hfstab` and only applies to `ℕ`-valued functions, but in return it gives an explicit bound on the
stabilisation index. -/
/-
**Nat.stabilises_of_antitone** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.stabilises_of_antitone {f : Nat -> Nat} (hfmono : Antitone f) (hfstab 
: forall m, f m = f (m + 1) -> f (m + 1) = f (m + 2)) : exists n <= f 0, forall 
m, n <= m -> f m = f n
参数：hfmono : Antitone f；hfstab : forall m, f m = f (m + 1) -> f (m + 1) = f (m + 
2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `LE.le.lt_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p

--- 原说明 ---
An antitone function `f : ℕ → ℕ` which is constant after stabilising for the fir
st time,
stabilises in at most `f 0` steps.

Compared to `WellFoundedLT.antitone_chain_condition`, this lemma requires the ex
tra hypothesis
`hfstab` and only applies to `ℕ`-valued functions, but in return it gives an exp
licit bound on the
stabilisation index.
-/
lemma Nat.stabilises_of_antitone {f : ℕ → ℕ} (hfmono : Antitone f)
    (hfstab : ∀ m, f m = f (m + 1) → f (m + 1) = f (m + 2)) :
    ∃ n ≤ f 0, ∀ m, n ≤ m → f m = f n := by
  induction h : f 0 using Nat.strongRecOn generalizing f with
  | ind n ih =>
    by_cases heq : f 0 = f 1
    · have flat (j : ℕ) : f j = f (j + 1) := by induction j with grind
      exact ⟨0, Nat.zero_le _, fun m _ => by induction m with grind⟩
    · have hlt : f 1 < f 0 := (hfmono (Nat.le_succ 0)).lt_of_ne' heq
      let g (i : ℕ) := f (i + 1)
      have hg_anti : Antitone g := by grind [Antitone]
      obtain ⟨p, hp, hp'⟩ := ih (f 1) (by grind) hg_anti (by grind) rfl
      refine ⟨p + 1, by omega, fun m hm => ?_⟩
      specialize hp' (m - 1) (by lia)
      grind

/-- A bounded monotone function `ℕ → ℕ` converges. -/
/-
**converges_of_monotone_of_bounded** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：converges_of_monotone_of_bounded {f : Nat -> Nat} (mono_f : Monotone f) {c
 : Nat} (hc : forall n, f n <= c) : exists b N, forall n >= N, f n = b
参数：mono_f : Monotone f；hc : forall n, f n <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_of_le_zero`：∀ {n : ℕ}, n ≤ 0 → n = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
A bounded monotone function `ℕ → ℕ` converges.
-/
lemma converges_of_monotone_of_bounded {f : ℕ → ℕ} (mono_f : Monotone f)
    {c : ℕ} (hc : ∀ n, f n ≤ c) : ∃ b N, ∀ n ≥ N, f n = b := by
  induction c with
  | zero => use 0, 0, fun n _ ↦ Nat.eq_zero_of_le_zero (hc n)
  | succ c ih =>
    by_cases! h : ∀ n, f n ≤ c
    · exact ih h
    · obtain ⟨N, hN⟩ := h
      replace hN : f N = c + 1 := by specialize hc N; lia
      use c + 1, N; intro n hn
      specialize mono_f hn; specialize hc n; lia
