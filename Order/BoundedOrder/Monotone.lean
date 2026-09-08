/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Monotone.Basic

/-!
# Monotone functions on bounded orders

-/

public section

assert_not_exists SemilatticeSup

open Function OrderDual

universe u v

variable {α : Type u} {β : Type v}

/-! ### Top, bottom element -/

section OrderTop

variable [PartialOrder α] [OrderTop α] [Preorder β] {f : α → β} {a b : α}

/-
**StrictMono.apply_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.apply_eq_top_iff (hf : StrictMono f) : f a = f ⊤ ↔ a = ⊤
参数：hf : StrictMono f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt_top_iff`：not_lt_top_iff : ¬a < ⊤ ↔ a = ⊤
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem StrictMono.apply_eq_top_iff (hf : StrictMono f) : f a = f ⊤ ↔ a = ⊤ :=
  ⟨fun h => not_lt_top_iff.1 fun ha => (hf ha).ne h, congr_arg _⟩
/-
**StrictAnti.apply_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAnti.apply_eq_top_iff (hf : StrictAnti f) : f a = f ⊤ ↔ a = ⊤
参数：hf : StrictAnti f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt_top_iff`：not_lt_top_iff : ¬a < ⊤ ↔ a = ⊤
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem StrictAnti.apply_eq_top_iff (hf : StrictAnti f) : f a = f ⊤ ↔ a = ⊤ :=
  ⟨fun h => not_lt_top_iff.1 fun ha => (hf ha).ne' h, congr_arg _⟩

end OrderTop

/-
**StrictMono.maximal_preimage_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.maximal_preimage_top [LinearOrder α] [Preorder β] [OrderTop β] 
{f : α -> β} (H : StrictMono f) {a} (h_top : f a = ⊤) (x : α) : x <= a
参数：H : StrictMono f；h_top : f a = ⊤；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.maximal_of_maximal_image`：StrictMono.maximal_of_maximal_image
 (hf : StrictMono f) {a} (hmax : forall p, p <= f a) (x : α) : x <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem StrictMono.maximal_preimage_top [LinearOrder α] [Preorder β] [OrderTop β] {f : α → β}
    (H : StrictMono f) {a} (h_top : f a = ⊤) (x : α) : x ≤ a :=
  H.maximal_of_maximal_image
    (fun p => by
      rw [h_top]
      exact le_top)
    x

section OrderBot

variable [PartialOrder α] [OrderBot α] [Preorder β] {f : α → β} {a b : α}

/-
**StrictMono.apply_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.apply_eq_bot_iff (hf : StrictMono f) : f a = f ⊥ ↔ a = ⊥
参数：hf : StrictMono f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.apply_eq_top_iff`：StrictMono.apply_eq_top_iff (hf : StrictMon
o f) : f a = f ⊤ ↔ a = ⊤
· 使用定理 `StrictMono.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f : α → β},   StrictMono f → StrictMono (⇑OrderDual.toDual ∘ f ∘
 ⇑Ord…
-/
theorem StrictMono.apply_eq_bot_iff (hf : StrictMono f) : f a = f ⊥ ↔ a = ⊥ :=
  hf.dual.apply_eq_top_iff
/-
**StrictAnti.apply_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAnti.apply_eq_bot_iff (hf : StrictAnti f) : f a = f ⊥ ↔ a = ⊥
参数：hf : StrictAnti f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.apply_eq_top_iff`：StrictAnti.apply_eq_top_iff (hf : StrictAnt
i f) : f a = f ⊤ ↔ a = ⊤
· 使用定理 `StrictAnti.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f : α → β},   StrictAnti f → StrictAnti (⇑OrderDual.toDual ∘ f ∘
 ⇑Ord…
-/
theorem StrictAnti.apply_eq_bot_iff (hf : StrictAnti f) : f a = f ⊥ ↔ a = ⊥ :=
  hf.dual.apply_eq_top_iff

end OrderBot

/-
**StrictMono.minimal_preimage_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.minimal_preimage_bot [LinearOrder α] [Preorder β] [OrderBot β] 
{f : α -> β} (H : StrictMono f) {a} (h_bot : f a = ⊥) (x : α) : a <= x
参数：H : StrictMono f；h_bot : f a = ⊥；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.minimal_of_minimal_image`：∀ {α : Type u} {β : Type v} [inst :
 LinearOrder α] [inst_1 : Preorder β] {f : α → β},   StrictMono f → ∀ {a : α}, (
∀ (p : β), f a ≤ p) → ∀ (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem StrictMono.minimal_preimage_bot [LinearOrder α] [Preorder β] [OrderBot β] {f : α → β}
    (H : StrictMono f) {a} (h_bot : f a = ⊥) (x : α) : a ≤ x :=
  H.minimal_of_minimal_image
    (fun p => by
      rw [h_bot]
      exact bot_le)
    x

section Logic

/-!
#### In this section we prove some properties about monotone and antitone operations on `Prop`
-/


section Preorder

variable [Preorder α]

/-
**monotone_and** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_and {p q : α -> Prop} (m_p : Monotone p) (m_q : Monotone q) : Mon
otone fun x => p x ∧ q x
参数：m_p : Monotone p；m_q : Monotone q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
-/
theorem monotone_and {p q : α → Prop} (m_p : Monotone p) (m_q : Monotone q) :
    Monotone fun x => p x ∧ q x :=
  fun _ _ h => And.imp (m_p h) (m_q h)

-- Note: by finish [monotone] doesn't work
/-
**monotone_or** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_or {p q : α -> Prop} (m_p : Monotone p) (m_q : Monotone q) : Mono
tone fun x => p x ∨ q x
参数：m_p : Monotone p；m_q : Monotone q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
-/
theorem monotone_or {p q : α → Prop} (m_p : Monotone p) (m_q : Monotone q) :
    Monotone fun x => p x ∨ q x :=
  fun _ _ h => Or.imp (m_p h) (m_q h)
/-
**monotone_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_le {x : α} : Monotone (x <= ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem monotone_le {x : α} : Monotone (x ≤ ·) := fun _ _ h' h => h.trans h'
/-
**monotone_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_lt {x : α} : Monotone (x < ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
theorem monotone_lt {x : α} : Monotone (x < ·) := fun _ _ h' h => h.trans_le h'
/-
**antitone_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitone_le {x : α} : Antitone (· <= x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem antitone_le {x : α} : Antitone (· ≤ x) := fun _ _ h' h => h'.trans h
/-
**antitone_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitone_lt {x : α} : Antitone (· < x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
-/
theorem antitone_lt {x : α} : Antitone (· < x) := fun _ _ h' h => h'.trans_lt h
/-
**Monotone.forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.forall {P : β -> α -> Prop} (hP : forall x, Monotone (P x)) : Mon
otone fun y => forall x, P x y
参数：hP : forall x, Monotone (P x)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Monotone.forall {P : β → α → Prop} (hP : ∀ x, Monotone (P x)) :
    Monotone fun y => ∀ x, P x y :=
  fun _ _ hy h x => hP x hy <| h x
/-
**Antitone.forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.forall {P : β -> α -> Prop} (hP : forall x, Antitone (P x)) : Ant
itone fun y => forall x, P x y
参数：hP : forall x, Antitone (P x)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Antitone.forall {P : β → α → Prop} (hP : ∀ x, Antitone (P x)) :
    Antitone fun y => ∀ x, P x y :=
  fun _ _ hy h x => hP x hy (h x)
/-
**Monotone.ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.ball {P : β -> α -> Prop} {s : Set β} (hP : forall x in s, Monoto
ne (P x)) : Monotone fun y => forall x in s, P x y
参数：hP : forall x in s, Monotone (P x)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Monotone.ball {P : β → α → Prop} {s : Set β} (hP : ∀ x ∈ s, Monotone (P x)) :
    Monotone fun y => ∀ x ∈ s, P x y := fun _ _ hy h x hx => hP x hx hy (h x hx)
/-
**Antitone.ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.ball {P : β -> α -> Prop} {s : Set β} (hP : forall x in s, Antito
ne (P x)) : Antitone fun y => forall x in s, P x y
参数：hP : forall x in s, Antitone (P x)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Antitone.ball {P : β → α → Prop} {s : Set β} (hP : ∀ x ∈ s, Antitone (P x)) :
    Antitone fun y => ∀ x ∈ s, P x y := fun _ _ hy h x hx => hP x hx hy (h x hx)
/-
**Monotone.exists** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.exists {P : β -> α -> Prop} (hP : forall x, Monotone (P x)) : Mon
otone fun y => exists x, P x y
参数：hP : forall x, Monotone (P x)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Monotone.exists {P : β → α → Prop} (hP : ∀ x, Monotone (P x)) :
    Monotone fun y => ∃ x, P x y :=
  fun _ _ hy ⟨x, hx⟩ ↦ ⟨x, hP x hy hx⟩
/-
**Antitone.exists** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.exists {P : β -> α -> Prop} (hP : forall x, Antitone (P x)) : Ant
itone fun y => exists x, P x y
参数：hP : forall x, Antitone (P x)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Antitone.exists {P : β → α → Prop} (hP : ∀ x, Antitone (P x)) :
    Antitone fun y => ∃ x, P x y :=
  fun _ _ hy ⟨x, hx⟩ ↦ ⟨x, hP x hy hx⟩
/-
**forall_ge_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_ge_iff {P : α -> Prop} {x₀ : α} (hP : Monotone P) : (forall x >= x₀
, P x) ↔ P x₀
参数：hP : Monotone P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem forall_ge_iff {P : α → Prop} {x₀ : α} (hP : Monotone P) :
    (∀ x ≥ x₀, P x) ↔ P x₀ :=
  ⟨fun H ↦ H x₀ le_rfl, fun H _ hx ↦ hP hx H⟩
/-
**forall_le_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_le_iff {P : α -> Prop} {x₀ : α} (hP : Antitone P) : (forall x <= x₀
, P x) ↔ P x₀
参数：hP : Antitone P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem forall_le_iff {P : α → Prop} {x₀ : α} (hP : Antitone P) :
    (∀ x ≤ x₀, P x) ↔ P x₀ :=
  ⟨fun H ↦ H x₀ le_rfl, fun H _ hx ↦ hP hx H⟩

end Preorder

end Logic

