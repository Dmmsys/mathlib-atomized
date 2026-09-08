/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Multiset.Count
public import Mathlib.Data.List.Count

/-!
# Sum and difference of multisets

This file defines the following operations on multisets:

* `Add (Multiset α)` instance: `s + t` adds the multiplicities of the elements of `s` and `t`
* `Sub (Multiset α)` instance: `s - t` subtracts the multiplicities of the elements of `s` and `t`
* `Multiset.erase`: `s.erase x` reduces the multiplicity of `x` in `s` by one.

## Notation (defined later)

* `s + t`: The multiset for which the number of occurrences of each `a` is the sum of the
  occurrences of `a` in `s` and `t`.
* `s - t`: The multiset for which the number of occurrences of each `a` is the difference of the
  occurrences of `a` in `s` and `t`.

-/

@[expose] public section

-- No algebra should be required
assert_not_exists Monoid

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

/-! ### Additive monoid -/

section add
variable {s t u : Multiset α}

/-- The sum of two multisets is the lift of the list append operation.
  This adds the multiplicities of each element,
  i.e. `count a (s + t) = count a s + count a t`. -/
/-
**Multiset.add** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：{α : Type u_1} → Multiset α → Multiset α → Multiset α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of two multisets is the lift of the list append operation.
  This adds the multiplicities of each element,
  i.e. `count a (s + t) = count a s + count a t`.
-/
protected def add (s₁ s₂ : Multiset α) : Multiset α :=
  (Quotient.liftOn₂ s₁ s₂ fun l₁ l₂ => ((l₁ ++ l₂ : List α) : Multiset α)) fun _ _ _ _ p₁ p₂ =>
    Quot.sound <| p₁.append p₂
/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (Multiset α) :=
  ⟨Multiset.add⟩

@[simp]
/-
**Multiset.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_add (s t : List α) : (s + t : Multiset α) = (s ++ t : List α)
参数：s t : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add (s t : List α) : (s + t : Multiset α) = (s ++ t : List α) :=
  rfl

@[simp]
/-
**Multiset.singleton_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：singleton_add (a : α) (s : Multiset α) : {a} + s = a ::ₘ s
参数：a : α；s : Multiset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem singleton_add (a : α) (s : Multiset α) : {a} + s = a ::ₘ s :=
  rfl
/-
**Multiset.add_le_add_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} {s t u : Multiset α}, s + t ≤ s + u ↔ t ≤ u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₃`：∀ {α : Sort uA} {β : Sort uB} {φ : Sort uC} {s₁ :
 Setoid α} {s₂ : Setoid β} {s₃ : Setoid φ}   {motive : Quotient s₁ → Quotient s₂
 → Quotient…
· 使用定理 `List.subperm_append_left`：∀ {α : Type u_1} {l₁ l₂ : List α} (l : List α)
, (l ++ l₁).Subperm (l ++ l₂) ↔ l₁.Subperm l₂
-/
protected lemma add_le_add_iff_left : s + t ≤ s + u ↔ t ≤ u :=
  Quotient.inductionOn₃ s t u fun _ _ _ => subperm_append_left _
/-
**Multiset.add_le_add_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} {s t u : Multiset α}, s + u ≤ t + u ↔ s ≤ t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₃`：∀ {α : Sort uA} {β : Sort uB} {φ : Sort uC} {s₁ :
 Setoid α} {s₂ : Setoid β} {s₃ : Setoid φ}   {motive : Quotient s₁ → Quotient s₂
 → Quotient…
· 使用定理 `List.subperm_append_right`：∀ {α : Type u_1} {l₁ l₂ : List α} (l : List α
), (l₁ ++ l).Subperm (l₂ ++ l) ↔ l₁.Subperm l₂
-/
protected lemma add_le_add_iff_right : s + u ≤ t + u ↔ s ≤ t :=
  Quotient.inductionOn₃ s t u fun _ _ _ => subperm_append_right _

protected alias ⟨le_of_add_le_add_left, add_le_add_left⟩ := Multiset.add_le_add_iff_left
protected alias ⟨le_of_add_le_add_right, add_le_add_right⟩ := Multiset.add_le_add_iff_right
/-
**Multiset.add_comm** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} (s t : Multiset α), s + t = t + s
参数：s t : Multiset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `List.perm_append_comm`：∀ {α : Type u_1} {l₁ l₂ : List α}, (l₁ ++ l₂).Per
m (l₂ ++ l₁)
-/
protected lemma add_comm (s t : Multiset α) : s + t = t + s :=
  Quotient.inductionOn₂ s t fun _ _ ↦ Quot.sound perm_append_comm
/-
**Multiset.add_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} (s t u : Multiset α), s + t + u = s + (t + u)
参数：s t u : Multiset α；t + u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₃`：∀ {α : Sort uA} {β : Sort uB} {φ : Sort uC} {s₁ :
 Setoid α} {s₂ : Setoid β} {s₃ : Setoid φ}   {motive : Quotient s₁ → Quotient s₂
 → Quotient…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
-/
protected lemma add_assoc (s t u : Multiset α) : s + t + u = s + (t + u) :=
  Quotient.inductionOn₃ s t u fun _ _ _ ↦ congr_arg _ <| append_assoc ..

@[simp high]
/-
**Multiset.zero_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} (s : Multiset α), 0 + s = s
参数：s : Multiset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
-/
protected lemma zero_add (s : Multiset α) : 0 + s = s := Quotient.inductionOn s fun _ ↦ rfl

@[simp high]
/-
**Multiset.add_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} (s : Multiset α), s + 0 = s
参数：s : Multiset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
-/
protected lemma add_zero (s : Multiset α) : s + 0 = s :=
  Quotient.inductionOn s fun l ↦ congr_arg _ <| append_nil l
/-
**Multiset.le_add_right** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：le_add_right (s t : Multiset α) : s <= s + t
参数：s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.add_zero`：∀ {α : Type u_1} (s : Multiset α), s + 0 = s
· 使用定理 `Multiset.add_le_add_left`：∀ {α : Type u_1} {s t u : Multiset α}, t ≤ u →
 s + t ≤ s + u
· 使用定理 `Multiset.zero_le`：zero_le (s : Multiset α) : 0 <= s
-/
lemma le_add_right (s t : Multiset α) : s ≤ s + t := by
  simpa using Multiset.add_le_add_left (zero_le t)
/-
**Multiset.le_add_left** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：le_add_left (s t : Multiset α) : s <= t + s
参数：s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.zero_add`：∀ {α : Type u_1} (s : Multiset α), 0 + s = s
· 使用定理 `Multiset.add_le_add_right`：∀ {α : Type u_1} {s t u : Multiset α}, s ≤ t 
→ s + u ≤ t + u
· 使用定理 `Multiset.zero_le`：zero_le (s : Multiset α) : 0 <= s
-/
lemma le_add_left (s t : Multiset α) : s ≤ t + s := by
  simpa using Multiset.add_le_add_right (zero_le t)
/-
**Multiset.subset_add_left** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：subset_add_left {s t : Multiset α} : s subseteq s + t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.subset_of_le`：subset_of_le : s <= t -> s subseteq t
· 使用引理 `Multiset.le_add_right`：le_add_right (s t : Multiset α) : s <= s + t
-/
lemma subset_add_left {s t : Multiset α} : s ⊆ s + t := subset_of_le <| le_add_right s t
/-
**Multiset.subset_add_right** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：subset_add_right {s t : Multiset α} : s subseteq t + s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.subset_of_le`：subset_of_le : s <= t -> s subseteq t
· 使用引理 `Multiset.le_add_left`：le_add_left (s t : Multiset α) : s <= t + s
-/
lemma subset_add_right {s t : Multiset α} : s ⊆ t + s := subset_of_le <| le_add_left s t
/-
**Multiset.le_iff_exists_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：le_iff_exists_add {s t : Multiset α} : s <= t ↔ exists u, t = s + u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.leInductionOn`：leInductionOn {C : Multiset α -> Multiset α -> P
rop} {s t : Multiset α} (h : s <= t) (H : forall {l₁ l₂ : List α}, l₁ <+ l₂ -> C
 l₁ l₂) : C …
· 使用定理 `List.Sublist.exists_perm_append`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.S
ublist l₂ → ∃ l, l₂.Perm (l₁ ++ l)
· 使用引理 `Multiset.le_add_right`：le_add_right (s t : Multiset α) : s <= s + t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem le_iff_exists_add {s t : Multiset α} : s ≤ t ↔ ∃ u, t = s + u :=
  ⟨fun h =>
    leInductionOn h fun s =>
      let ⟨l, p⟩ := s.exists_perm_append
      ⟨l, Quot.sound p⟩,
    fun ⟨_u, e⟩ => e.symm ▸ le_add_right _ _⟩

@[simp]
/-
**Multiset.cons_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：cons_add (a : α) (s t : Multiset α) : a ::ₘ s + t = a ::ₘ (s + t)
参数：a : α；s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.singleton_add`：singleton_add (a : α) (s : Multiset α) : {a} + s
 = a ::ₘ s
· 使用定理 `Multiset.add_assoc`：∀ {α : Type u_1} (s t u : Multiset α), s + t + u = s
 + (t + u)
-/
theorem cons_add (a : α) (s t : Multiset α) : a ::ₘ s + t = a ::ₘ (s + t) := by
  rw [← singleton_add, ← singleton_add, Multiset.add_assoc]

@[simp]
/-
**Multiset.add_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：add_cons (a : α) (s t : Multiset α) : s + a ::ₘ t = a ::ₘ (s + t)
参数：a : α；s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.add_comm`：∀ {α : Type u_1} (s t : Multiset α), s + t = t + s
· 使用定理 `Multiset.cons_add`：cons_add (a : α) (s t : Multiset α) : a ::ₘ s + t = a
 ::ₘ (s + t)
-/
theorem add_cons (a : α) (s t : Multiset α) : s + a ::ₘ t = a ::ₘ (s + t) := by
  rw [Multiset.add_comm, cons_add, Multiset.add_comm]

@[simp, grind =]
/-
**Multiset.mem_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_add {a : α} {s t : Multiset α} : a in s + t ↔ a in s ∨ a in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `List.mem_append`：∀ {α : Type u_1} {a : α} {s t : List α}, a ∈ s ++ t ↔ a
 ∈ s ∨ a ∈ t
-/
theorem mem_add {a : α} {s t : Multiset α} : a ∈ s + t ↔ a ∈ s ∨ a ∈ t :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ => mem_append

variable (p : α → Prop) [DecidablePred p]

@[simp]
/-
**Multiset.countP_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：countP_add (s t) : countP p (s + t) = countP p s + countP p t
参数：s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `List.countP_append`：∀ {α : Type u_1} {p : α → Bool} {l₁ l₂ : List α}, Li
st.countP p (l₁ ++ l₂) = List.countP p l₁ + List.countP p l₂
-/
theorem countP_add (s t) : countP p (s + t) = countP p s + countP p t :=
  Quotient.inductionOn₂ s t fun _ _ => countP_append

variable [DecidableEq α] in
@[simp]
/-
**Multiset.count_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_add (a : α) : forall s t, count a (s + t) = count a s + count a t
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.countP_add`：countP_add (s t) : countP p (s + t) = countP p s + 
countP p t
-/
theorem count_add (a : α) : ∀ s t, count a (s + t) = count a s + count a t :=
  countP_add _
/-
**Multiset.add_left_inj** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} {s t u : Multiset α}, s + u = t + u ↔ s = t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Multiset.count_add`：count_add (a : α) : forall s t, count a (s + t) = co
unt a s + count a t
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma add_left_inj : s + u = t + u ↔ s = t := by classical simp [Multiset.ext]
/-
**Multiset.add_right_inj** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} {s t u : Multiset α}, s + t = s + u ↔ t = u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Multiset.count_add`：count_add (a : α) : forall s t, count a (s + t) = co
unt a s + count a t
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma add_right_inj : s + t = s + u ↔ t = u := by classical simp [Multiset.ext]

@[simp]
/-
**Multiset.card_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_add (s t : Multiset α) : card (s + t) = card s + card t
参数：s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
-/
theorem card_add (s t : Multiset α) : card (s + t) = card s + card t :=
  Quotient.inductionOn₂ s t fun _ _ => length_append

end add

/-! ### Erasing one copy of an element -/

section Erase

variable [DecidableEq α] {s t : Multiset α} {a b : α}

/-- `erase s a` is the multiset that subtracts 1 from the multiplicity of `a`. -/
/-
**Multiset.erase** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：erase (s : Multiset α) (a : α) : Multiset α
参数：s : Multiset α；a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`erase s a` is the multiset that subtracts 1 from the multiplicity of `a`.
-/
def erase (s : Multiset α) (a : α) : Multiset α :=
  Quot.liftOn s (fun l => (l.erase a : Multiset α)) fun _l₁ _l₂ p => Quot.sound (p.erase a)

@[simp]
/-
**Multiset.coe_erase** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_erase (l : List α) (a : α) : erase (l : Multiset α) a = l.erase a
参数：l : List α；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_erase (l : List α) (a : α) : erase (l : Multiset α) a = l.erase a :=
  rfl

@[simp]
/-
**Multiset.erase_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：erase_zero (a : α) : (0 : Multiset α).erase a = 0
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_zero (a : α) : (0 : Multiset α).erase a = 0 :=
  rfl

@[simp]
/-
**Multiset.erase_cons_head** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：erase_cons_head (a : α) (s : Multiset α) : (a ::ₘ s).erase a = s
参数：a : α；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.erase_cons_head`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] (a :
 α) (l : List α), (a :: l).erase a = l
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem erase_cons_head (a : α) (s : Multiset α) : (a ::ₘ s).erase a = s :=
  Quot.inductionOn s fun l => congr_arg _ <| List.erase_cons_head a l

@[simp]
/-
**Multiset.erase_cons_tail** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：erase_cons_tail {a b : α} (s : Multiset α) (h : b != a) : (b ::ₘ s).erase 
a = b ::ₘ s.erase a
参数：s : Multiset α；h : b != a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.erase_cons_tail`：∀ {α : Type u_1} [inst : BEq α] {a b : α} {l : Lis
t α}, ¬(b == a) = true → (b :: l).erase a = b :: l.erase a
· 使用定理 `not_beq_of_ne`：not_beq_of_ne {α : Type*} [BEq α] [LawfulBEq α] {a b : α}
 (ne : a != b) : ¬(a == b)
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem erase_cons_tail {a b : α} (s : Multiset α) (h : b ≠ a) :
    (b ::ₘ s).erase a = b ::ₘ s.erase a :=
  Quot.inductionOn s fun _ => congr_arg _ <| List.erase_cons_tail (not_beq_of_ne h)

@[simp]
/-
**Multiset.erase_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：erase_singleton (a : α) : ({a} : Multiset α).erase a = 0
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.erase_cons_head`：erase_cons_head (a : α) (s : Multiset α) : (a 
::ₘ s).erase a = s
-/
theorem erase_singleton (a : α) : ({a} : Multiset α).erase a = 0 :=
  erase_cons_head a 0

@[simp]
/-
**Multiset.erase_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：erase_of_notMem {a : α} {s : Multiset α} : a ∉ s -> s.erase a = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.erase_of_not_mem`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a 
: α} {l : List α}, a ∉ l → l.erase a = l
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem erase_of_notMem {a : α} {s : Multiset α} : a ∉ s → s.erase a = s :=
  Quot.inductionOn s fun _l h => congr_arg _ <| List.erase_of_not_mem h

@[simp]
/-
**Multiset.cons_erase** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：cons_erase {s : Multiset α} {a : α} : a in s -> a ::ₘ s.erase a = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁
· 使用定理 `List.perm_cons_erase`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a :
 α} {l : List α}, a ∈ l → l.Perm (a :: l.erase a)
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem cons_erase {s : Multiset α} {a : α} : a ∈ s → a ::ₘ s.erase a = s :=
  Quot.inductionOn s fun _l h => Quot.sound (perm_cons_erase h).symm
/-
**Multiset.erase_cons_tail_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：erase_cons_tail_of_mem (h : a in s) : (b ::ₘ s).erase a = b ::ₘ s.erase a
参数：h : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.erase_cons_head`：erase_cons_head (a : α) (s : Multiset α) : (a 
::ₘ s).erase a = s
· 使用定理 `Multiset.cons_erase`：cons_erase {s : Multiset α} {a : α} : a in s -> a :
:ₘ s.erase a = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.erase_cons_tail`：erase_cons_tail {a b : α} (s : Multiset α) (h 
: b != a) : (b ::ₘ s).erase a = b ::ₘ s.erase a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem erase_cons_tail_of_mem (h : a ∈ s) :
    (b ::ₘ s).erase a = b ::ₘ s.erase a := by
  rcases eq_or_ne a b with rfl | hab
  · simp [cons_erase h]
  · exact s.erase_cons_tail hab.symm
/-
**Multiset.le_cons_erase** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：le_cons_erase (s : Multiset α) (a : α) : s <= a ::ₘ s.erase a
参数：s : Multiset α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.cons_erase`：cons_erase {s : Multiset α} {a : α} : a in s -> a :
:ₘ s.erase a = s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.erase_of_notMem`：erase_of_notMem {a : α} {s : Multiset α} : a ∉
 s -> s.erase a = s
· 使用定理 `Multiset.le_cons_self`：le_cons_self (s : Multiset α) (a : α) : s <= a ::
ₘ s
-/
theorem le_cons_erase (s : Multiset α) (a : α) : s ≤ a ::ₘ s.erase a :=
  if h : a ∈ s then le_of_eq (cons_erase h).symm
  else by rw [erase_of_notMem h]; apply le_cons_self
/-
**Multiset.add_singleton_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：add_singleton_eq_iff {s t : Multiset α} {a : α} : s + {a} = t ↔ a in t ∧ s
 = t.erase a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.add_comm`：∀ {α : Type u_1} (s t : Multiset α), s + t = t + s
· 使用定理 `Multiset.singleton_add`：singleton_add (a : α) (s : Multiset α) : {a} + s
 = a ::ₘ s
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.erase_cons_head`：erase_cons_head (a : α) (s : Multiset α) : (a 
::ₘ s).erase a = s
· 使用定理 `Multiset.cons_erase`：cons_erase {s : Multiset α} {a : α} : a in s -> a :
:ₘ s.erase a = s
-/
theorem add_singleton_eq_iff {s t : Multiset α} {a : α} : s + {a} = t ↔ a ∈ t ∧ s = t.erase a := by
  rw [Multiset.add_comm, singleton_add]
  constructor
  · rintro rfl
    exact ⟨s.mem_cons_self a, (s.erase_cons_head a).symm⟩
  · rintro ⟨h, rfl⟩
    exact cons_erase h
/-
**Multiset.erase_add_left_pos** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：erase_add_left_pos {a : α} {s : Multiset α} (t) : a in s -> (s + t).erase 
a = s.erase a + t
参数：t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.erase_append_left`：∀ {α : Type u_1} [inst : BEq α] {a : α} [LawfulB
Eq α] {l₁ : List α} (l₂ : List α),   a ∈ l₁ → (l₁ ++ l₂).erase a = l₁.erase a ++
 l₂
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem erase_add_left_pos {a : α} {s : Multiset α} (t) : a ∈ s → (s + t).erase a = s.erase a + t :=
  Quotient.inductionOn₂ s t fun _l₁ l₂ h => congr_arg _ <| erase_append_left l₂ h
/-
**Multiset.erase_add_right_pos** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：erase_add_right_pos {a : α} (s) (h : a in t) : (s + t).erase a = s + t.era
se a
参数：s；h : a in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.add_comm`：∀ {α : Type u_1} (s t : Multiset α), s + t = t + s
· 使用定理 `Multiset.erase_add_left_pos`：erase_add_left_pos {a : α} {s : Multiset α}
 (t) : a in s -> (s + t).erase a = s.erase a + t
-/
theorem erase_add_right_pos {a : α} (s) (h : a ∈ t) : (s + t).erase a = s + t.erase a := by
  rw [Multiset.add_comm, erase_add_left_pos s h, Multiset.add_comm]
/-
**Multiset.erase_add_right_neg** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：erase_add_right_neg {a : α} {s : Multiset α} (t) : a ∉ s -> (s + t).erase 
a = s + t.erase a
参数：t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.erase_append_right`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {
a : α} {l₁ : List α} (l₂ : List α),   a ∉ l₁ → (l₁ ++ l₂).erase a = l₁ ++ l₂.era
se a
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem erase_add_right_neg {a : α} {s : Multiset α} (t) :
    a ∉ s → (s + t).erase a = s + t.erase a :=
  Quotient.inductionOn₂ s t fun _l₁ l₂ h => congr_arg _ <| erase_append_right l₂ h
/-
**Multiset.erase_add_left_neg** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：erase_add_left_neg {a : α} (s) (h : a ∉ t) : (s + t).erase a = s.erase a +
 t
参数：s；h : a ∉ t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.add_comm`：∀ {α : Type u_1} (s t : Multiset α), s + t = t + s
· 使用定理 `Multiset.erase_add_right_neg`：erase_add_right_neg {a : α} {s : Multiset 
α} (t) : a ∉ s -> (s + t).erase a = s + t.erase a
-/
theorem erase_add_left_neg {a : α} (s) (h : a ∉ t) : (s + t).erase a = s.erase a + t := by
  rw [Multiset.add_comm, erase_add_right_neg s h, Multiset.add_comm]
/-
**Multiset.erase_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：erase_le (a : α) (s : Multiset α) : s.erase a <= s
参数：a : α；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.Sublist.subperm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ →
 l₁.Subperm l₂
· 使用定理 `List.erase_sublist`：∀ {α : Type u_1} [inst : BEq α] {a : α} {l : List α}
, (l.erase a).Sublist l
-/
theorem erase_le (a : α) (s : Multiset α) : s.erase a ≤ s :=
  Quot.inductionOn s fun _ => erase_sublist.subperm

@[simp]
/-
**Multiset.erase_lt** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：erase_lt {a : α} {s : Multiset α} : s.erase a < s ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `Multiset.erase_of_notMem`：erase_of_notMem {a : α} {s : Multiset α} : a ∉
 s -> s.erase a = s
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.cons_erase`：cons_erase {s : Multiset α} {a : α} : a in s -> a :
:ₘ s.erase a = s
· 使用定理 `Multiset.lt_cons_self`：lt_cons_self (s : Multiset α) (a : α) : s < a ::ₘ
 s
-/
theorem erase_lt {a : α} {s : Multiset α} : s.erase a < s ↔ a ∈ s :=
  ⟨fun h => not_imp_comm.1 erase_of_notMem (ne_of_lt h), fun h => by
    simpa [h] using lt_cons_self (s.erase a) a⟩
/-
**Multiset.erase_subset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：erase_subset (a : α) (s : Multiset α) : s.erase a subseteq s
参数：a : α；s : Multiset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.subset_of_le`：subset_of_le : s <= t -> s subseteq t
· 使用定理 `Multiset.erase_le`：erase_le (a : α) (s : Multiset α) : s.erase a <= s
-/
theorem erase_subset (a : α) (s : Multiset α) : s.erase a ⊆ s :=
  subset_of_le (erase_le a s)
/-
**Multiset.mem_erase_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_erase_of_ne {a b : α} {s : Multiset α} (ab : a != b) : a in s.erase b 
↔ a in s
参数：ab : a != b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.mem_erase_of_ne`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a b
 : α} {l : List α}, a ≠ b → (a ∈ l.erase b ↔ a ∈ l)
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem mem_erase_of_ne {a b : α} {s : Multiset α} (ab : a ≠ b) : a ∈ s.erase b ↔ a ∈ s :=
  Quot.inductionOn s fun _l => List.mem_erase_of_ne ab
/-
**Multiset.mem_of_mem_erase** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_of_mem_erase {a b : α} {s : Multiset α} : a in s.erase b -> a in s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_of_subset`：mem_of_subset {s t : Multiset α} {a : α} (h : s 
subseteq t) : a in s -> a in t
· 使用定理 `Multiset.erase_subset`：erase_subset (a : α) (s : Multiset α) : s.erase a
 subseteq s
-/
theorem mem_of_mem_erase {a b : α} {s : Multiset α} : a ∈ s.erase b → a ∈ s :=
  mem_of_subset (erase_subset _ _)
/-
**Multiset.erase_comm** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：erase_comm (s : Multiset α) (a b : α) : (s.erase a).erase b = (s.erase b).
erase a
参数：s : Multiset α；a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.erase_comm`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] (a b : α)
 {l : List α}, (l.erase a).erase b = (l.erase b).erase a
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem erase_comm (s : Multiset α) (a b : α) : (s.erase a).erase b = (s.erase b).erase a :=
  Quot.inductionOn s fun l => congr_arg _ <| l.erase_comm a b
/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : RightCommutative erase (α := α) := ⟨erase_comm⟩

@[gcongr]
/-
**Multiset.erase_le_erase** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：erase_le_erase {s t : Multiset α} (a : α) (h : s <= t) : s.erase a <= t.er
ase a
参数：a : α；h : s <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.leInductionOn`：leInductionOn {C : Multiset α -> Multiset α -> P
rop} {s t : Multiset α} (h : s <= t) (H : forall {l₁ l₂ : List α}, l₁ <+ l₂ -> C
 l₁ l₂) : C …
· 使用定理 `List.Sublist.subperm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ →
 l₁.Subperm l₂
· 使用定理 `List.Sublist.erase`：∀ {α : Type u_1} [inst : BEq α] (a : α) {l₁ l₂ : Lis
t α}, l₁.Sublist l₂ → (l₁.erase a).Sublist (l₂.erase a)
-/
theorem erase_le_erase {s t : Multiset α} (a : α) (h : s ≤ t) : s.erase a ≤ t.erase a :=
  leInductionOn h fun h => (h.erase _).subperm
/-
**Multiset.erase_le_iff_le_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：erase_le_iff_le_cons {s t : Multiset α} {a : α} : s.erase a <= t ↔ s <= a 
::ₘ t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Multiset.le_cons_erase`：le_cons_erase (s : Multiset α) (a : α) : s <= a 
::ₘ s.erase a
· 使用定理 `Multiset.cons_le_cons`：cons_le_cons (a : α) : s <= t -> a ::ₘ s <= a ::ₘ
 t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.cons_le_cons_iff`：∀ {α : Type u_1} {s t : Multiset α} (a : α), 
a ::ₘ s ≤ a ::ₘ t ↔ s ≤ t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.cons_erase`：cons_erase {s : Multiset α} {a : α} : a in s -> a :
:ₘ s.erase a = s
· 使用定理 `Multiset.erase_le`：erase_le (a : α) (s : Multiset α) : s.erase a <= s
· 使用定理 `Multiset.le_cons_of_notMem`：le_cons_of_notMem (m : a ∉ s) : s <= a ::ₘ t
 ↔ s <= t
-/
theorem erase_le_iff_le_cons {s t : Multiset α} {a : α} : s.erase a ≤ t ↔ s ≤ a ::ₘ t :=
  ⟨fun h => le_trans (le_cons_erase _ _) (cons_le_cons _ h), fun h =>
    if m : a ∈ s then by rw [← cons_erase m] at h; exact (cons_le_cons_iff _).1 h
    else le_trans (erase_le _ _) ((le_cons_of_notMem m).1 h)⟩

@[simp]
/-
**Multiset.card_erase_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_erase_of_mem {a : α} {s : Multiset α} : a in s -> card (s.erase a) = 
pred (card s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.length_erase_of_mem`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] 
{a : α} {l : List α}, a ∈ l → (l.erase a).length = l.length - 1
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem card_erase_of_mem {a : α} {s : Multiset α} : a ∈ s → card (s.erase a) = pred (card s) :=
  Quot.inductionOn s fun _l => length_erase_of_mem

-- @[simp] -- removed because LHS is not in simp normal form
/-
**Multiset.card_erase_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_erase_add_one {a : α} {s : Multiset α} : a in s -> card (s.erase a) +
 1 = card s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.length_erase_add_one`：length_erase_add_one {a : α} {l : List α} (h 
: a in l) : (l.erase a).length + 1 = l.length
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem card_erase_add_one {a : α} {s : Multiset α} : a ∈ s → card (s.erase a) + 1 = card s :=
  Quot.inductionOn s fun _l => length_erase_add_one
/-
**Multiset.card_erase_lt_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_erase_lt_of_mem {a : α} {s : Multiset α} : a in s -> card (s.erase a)
 < card s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_lt_card`：card_lt_card {s t : Multiset α} (h : s < t) : car
d s < card t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.erase_lt`：erase_lt {a : α} {s : Multiset α} : s.erase a < s ↔ a
 in s
-/
theorem card_erase_lt_of_mem {a : α} {s : Multiset α} : a ∈ s → card (s.erase a) < card s :=
  fun h => card_lt_card (erase_lt.mpr h)
/-
**Multiset.card_erase_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_erase_le {a : α} {s : Multiset α} : card (s.erase a) <= card s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_le_card`：card_le_card {s t : Multiset α} (h : s <= t) : ca
rd s <= card t
· 使用定理 `Multiset.erase_le`：erase_le (a : α) (s : Multiset α) : s.erase a <= s
-/
theorem card_erase_le {a : α} {s : Multiset α} : card (s.erase a) ≤ card s :=
  card_le_card (erase_le a s)
/-
**Multiset.card_erase_eq_ite** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_erase_eq_ite {a : α} {s : Multiset α} : card (s.erase a) = if a in s 
then pred (card s) else card s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.card_erase_of_mem`：card_erase_of_mem {a : α} {s : Multiset α} :
 a in s -> card (s.erase a) = pred (card s)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Multiset.erase_of_notMem`：erase_of_notMem {a : α} {s : Multiset α} : a ∉
 s -> s.erase a = s
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem card_erase_eq_ite {a : α} {s : Multiset α} :
    card (s.erase a) = if a ∈ s then pred (card s) else card s := by
  by_cases h : a ∈ s
  · rwa [card_erase_of_mem h, if_pos]
  · rwa [erase_of_notMem h, if_neg]

@[simp]
/-
**Multiset.count_erase_self** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_erase_self (a : α) (s : Multiset α) : count a (erase s a) = count a 
s - 1
参数：a : α；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.coe_count`：coe_count (a : α) (l : List α) : count a (ofList l) 
= l.count a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.count_erase_self`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a 
: α} {l : List α}, List.count a (l.erase a) = List.count a l - 1
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem count_erase_self (a : α) (s : Multiset α) : count a (erase s a) = count a s - 1 :=
  Quotient.inductionOn s fun l => by
    convert! List.count_erase_self (a := a) (l := l) <;> rw [← coe_count] <;> simp

@[simp]
/-
**Multiset.count_erase_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_erase_of_ne {a b : α} (ab : a != b) (s : Multiset α) : count a (eras
e s b) = count a s
参数：ab : a != b；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.coe_count`：coe_count (a : α) (l : List α) : count a (ofList l) 
= l.count a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.count_erase_of_ne`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a
 b : α},   a ≠ b → ∀ {l : List α}, List.count a (l.erase b) = List.count a l
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem count_erase_of_ne {a b : α} (ab : a ≠ b) (s : Multiset α) :
    count a (erase s b) = count a s :=
  Quotient.inductionOn s fun l => by
    convert! List.count_erase_of_ne ab (l := l) <;> rw [← coe_count] <;> simp

end Erase

/-! ### Subtraction -/

section sub
variable [DecidableEq α] {s t u : Multiset α} {a : α}

/-- `s - t` is the multiset such that `count a (s - t) = count a s - count a t` for all `a`.
(note that it is truncated subtraction, so `count a (s - t) = 0` if `count a s ≤ count a t`). -/
/-
**Multiset.sub** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：{α : Type u_1} → [DecidableEq α] → Multiset α → Multiset α → Multiset α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`s - t` is the multiset such that `count a (s - t) = count a s - count a t` for 
all `a`.
(note that it is truncated subtraction, so `count a (s - t) = 0` if `count a s ≤
 count a t`).
-/
protected def sub (s t : Multiset α) : Multiset α :=
  (Quotient.liftOn₂ s t fun l₁ l₂ => (l₁.diff l₂ : Multiset α)) fun _v₁ _v₂ _w₁ _w₂ p₁ p₂ =>
    Quot.sound <| p₁.diff p₂
/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (Multiset α) := ⟨.sub⟩

@[simp]
/-
**Multiset.coe_sub** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：coe_sub (s t : List α) : (s - t : Multiset α) = s.diff t
参数：s t : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_sub (s t : List α) : (s - t : Multiset α) = s.diff t :=
  rfl

/-- This is a special case of `tsub_zero`, which should be used instead of this.
This is needed to prove `OrderedSub (Multiset α)`. -/
@[simp high]
/-
**Multiset.sub_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (s : Multiset α), s - 0 = s
参数：s : Multiset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q

--- 原说明 ---
This is a special case of `tsub_zero`, which should be used instead of this.
This is needed to prove `OrderedSub (Multiset α)`.
-/
protected lemma sub_zero (s : Multiset α) : s - 0 = s :=
  Quot.inductionOn s fun _l => rfl

@[simp]
/-
**Multiset.sub_cons** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：sub_cons (a : α) (s t : Multiset α) : s - a ::ₘ t = s.erase a - t
参数：a : α；s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.diff_cons`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] (l₁ l₂ : L
ist α) (a : α), l₁.diff (a :: l₂) = (l₁.erase a).diff l₂
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
lemma sub_cons (a : α) (s t : Multiset α) : s - a ::ₘ t = s.erase a - t :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ => congr_arg _ <| diff_cons _ _ _
/-
**Multiset.zero_sub** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (t : Multiset α), 0 - t = 0
参数：t : Multiset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Multiset.sub_cons`：sub_cons (a : α) (s t : Multiset α) : s - a ::ₘ t = s
.erase a - t
· 使用定理 `Multiset.erase_of_notMem`：erase_of_notMem {a : α} {s : Multiset α} : a ∉
 s -> s.erase a = s
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma zero_sub (t : Multiset α) : 0 - t = 0 :=
  Multiset.induction_on t rfl fun a s ih => by simp [ih]

@[simp]
/-
**Multiset.countP_sub** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：countP_sub {s t : Multiset α} : t <= s -> forall (p : α -> Prop) [Decidabl
ePred p], countP p (s - t) = countP p s - countP p t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用引理 `List.countP_diff`：countP_diff (hl : l₂ <+~ l₁) (p : α -> Bool) : countP 
p (l₁.diff l₂) = countP p l₁ - countP p l₂
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
lemma countP_sub {s t : Multiset α} :
    t ≤ s → ∀ (p : α → Prop) [DecidablePred p], countP p (s - t) = countP p s - countP p t :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ hl _ _ ↦ List.countP_diff hl _

@[simp]
/-
**Multiset.count_sub** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：count_sub (a : α) (s t : Multiset α) : count a (s - t) = count a s - count
 a t
参数：a : α；s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.coe_count`：coe_count (a : α) (l : List α) : count a (ofList l) 
= l.count a
· 使用定理 `List.count_diff`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] (a : α) (
l₁ l₂ : List α),   List.count a (l₁.diff l₂) = List.count a l₁ - List.count a l₂
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma count_sub (a : α) (s t : Multiset α) : count a (s - t) = count a s - count a t :=
  Quotient.inductionOn₂ s t <| by simp [List.count_diff]

/-- This is a special case of `tsub_le_iff_right`, which should be used instead of this.
This is needed to prove `OrderedSub (Multiset α)`. -/
/-
**Multiset.sub_le_iff_le_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t u : Multiset α}, s - t ≤ u ↔ 
s ≤ u + t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.sub_zero`：∀ {α : Type u_1} [inst : DecidableEq α] (s : Multiset
 α), s - 0 = s
· 使用定理 `Multiset.add_zero`：∀ {α : Type u_1} (s : Multiset α), s + 0 = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `Multiset.sub_cons`：sub_cons (a : α) (s t : Multiset α) : s - a ::ₘ t = s
.erase a - t
· 使用定理 `Multiset.add_cons`：add_cons (a : α) (s t : Multiset α) : s + a ::ₘ t = a
 ::ₘ (s + t)

--- 原说明 ---
This is a special case of `tsub_le_iff_right`, which should be used instead of t
his.
This is needed to prove `OrderedSub (Multiset α)`.
-/
protected lemma sub_le_iff_le_add : s - t ≤ u ↔ s ≤ u + t := by
  induction t using Multiset.induction_on generalizing s with
  | empty => simp [Multiset.sub_zero]
  | cons a s IH => simp [IH, erase_le_iff_le_cons]

/-- This is a special case of `tsub_le_iff_left`, which should be used instead of this. -/
/-
**Multiset.sub_le_iff_le_add'** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t u : Multiset α}, s - t ≤ u ↔ 
s ≤ t + u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.sub_le_iff_le_add`：∀ {α : Type u_1} [inst : DecidableEq α] {s t
 u : Multiset α}, s - t ≤ u ↔ s ≤ u + t
· 使用定理 `Multiset.add_comm`：∀ {α : Type u_1} (s t : Multiset α), s + t = t + s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
This is a special case of `tsub_le_iff_left`, which should be used instead of th
is.
-/
protected lemma sub_le_iff_le_add' : s - t ≤ u ↔ s ≤ t + u := by
  rw [Multiset.sub_le_iff_le_add, Multiset.add_comm]
/-
**Multiset.sub_le_self** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (s t : Multiset α), s - t ≤ s
参数：s t : Multiset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.sub_le_iff_le_add`：∀ {α : Type u_1} [inst : DecidableEq α] {s t
 u : Multiset α}, s - t ≤ u ↔ s ≤ u + t
· 使用引理 `Multiset.le_add_right`：le_add_right (s t : Multiset α) : s <= s + t
-/
protected theorem sub_le_self (s t : Multiset α) : s - t ≤ s := by
  rw [Multiset.sub_le_iff_le_add]
  exact le_add_right _ _
/-
**Multiset.add_sub_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t u : Multiset α}, u ≤ t → s + 
t - u = s + (t - u)
参数：t - u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.ext'`：ext' {s t : Multiset α} : (forall a, count a s = count a 
t) -> s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Multiset.count_sub`：count_sub (a : α) (s t : Multiset α) : count a (s - 
t) = count a s - count a t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.count_add`：count_add (a : α) : forall s t, count a (s + t) = co
unt a s + count a t
· 使用定理 `Nat.add_sub_assoc`：∀ {m k : ℕ}, k ≤ m → ∀ (n : ℕ), n + m - k = n + (m - 
k)
· 使用定理 `Multiset.count_le_of_le`：count_le_of_le (a : α) {s t} : s <= t -> count 
a s <= count a t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma add_sub_assoc (hut : u ≤ t) : s + t - u = s + (t - u) := by
  ext a; simp [Nat.add_sub_assoc <| count_le_of_le _ hut]
/-
**Multiset.add_sub_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Multiset α}, t ≤ s → s - t 
+ t = s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.ext'`：ext' {s t : Multiset α} : (forall a, count a s = count a 
t) -> s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count_add`：count_add (a : α) : forall s t, count a (s + t) = co
unt a s + count a t
· 使用引理 `Multiset.count_sub`：count_sub (a : α) (s t : Multiset α) : count a (s - 
t) = count a s - count a t
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Multiset.count_le_of_le`：count_le_of_le (a : α) {s t} : s <= t -> count 
a s <= count a t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma add_sub_cancel (hts : t ≤ s) : s - t + t = s := by
  ext a; simp [Nat.sub_add_cancel <| count_le_of_le _ hts]
/-
**Multiset.sub_add_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Multiset α}, t ≤ s → s - t 
+ t = s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.ext'`：ext' {s t : Multiset α} : (forall a, count a s = count a 
t) -> s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count_add`：count_add (a : α) : forall s t, count a (s + t) = co
unt a s + count a t
· 使用引理 `Multiset.count_sub`：count_sub (a : α) (s t : Multiset α) : count a (s - 
t) = count a s - count a t
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Multiset.count_le_of_le`：count_le_of_le (a : α) {s t} : s <= t -> count 
a s <= count a t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma sub_add_cancel (hts : t ≤ s) : s - t + t = s := by
  ext a; simp [Nat.sub_add_cancel <| count_le_of_le _ hts]
/-
**Multiset.sub_add_eq_sub_sub** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t u : Multiset α}, s - (t + u) 
= s - t - u
参数：t + u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.ext'`：ext' {s t : Multiset α} : (forall a, count a s = count a 
t) -> s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Multiset.count_sub`：count_sub (a : α) (s t : Multiset α) : count a (s - 
t) = count a s - count a t
· 使用定理 `Multiset.count_add`：count_add (a : α) : forall s t, count a (s + t) = co
unt a s + count a t
· 使用定理 `Nat.sub_add_eq`：∀ (a b c : ℕ), a - (b + c) = a - b - c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma sub_add_eq_sub_sub : s - (t + u) = s - t - u := by ext; simp [Nat.sub_add_eq]
/-
**Multiset.le_sub_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Multiset α}, s ≤ s - t + t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.sub_le_iff_le_add`：∀ {α : Type u_1} [inst : DecidableEq α] {s t
 u : Multiset α}, s - t ≤ u ↔ s ≤ u + t
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
protected lemma le_sub_add : s ≤ s - t + t := Multiset.sub_le_iff_le_add.1 le_rfl
/-
**Multiset.le_add_sub** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Multiset α}, s ≤ t + (s - t
)
参数：s - t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.sub_le_iff_le_add'`：∀ {α : Type u_1} [inst : DecidableEq α] {s 
t u : Multiset α}, s - t ≤ u ↔ s ≤ t + u
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
protected lemma le_add_sub : s ≤ t + (s - t) := Multiset.sub_le_iff_le_add'.1 le_rfl
/-
**Multiset.sub_le_sub_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t u : Multiset α}, s ≤ t → s - 
u ≤ t - u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.sub_le_iff_le_add'`：∀ {α : Type u_1} [inst : DecidableEq α] {s 
t u : Multiset α}, s - t ≤ u ↔ s ≤ t + u
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Multiset.le_add_sub`：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Mult
iset α}, s ≤ t + (s - t)
-/
protected lemma sub_le_sub_right (hst : s ≤ t) : s - u ≤ t - u :=
  Multiset.sub_le_iff_le_add'.mpr <| hst.trans Multiset.le_add_sub
/-
**Multiset.add_sub_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Multiset α}, s + t - t = s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.ext'`：ext' {s t : Multiset α} : (forall a, count a s = count a 
t) -> s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Multiset.count_sub`：count_sub (a : α) (s t : Multiset α) : count a (s - 
t) = count a s - count a t
· 使用定理 `Multiset.count_add`：count_add (a : α) : forall s t, count a (s + t) = co
unt a s + count a t
· 使用定理 `Nat.add_sub_cancel`：∀ (n m : ℕ), n + m - m = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma add_sub_cancel_right : s + t - t = s := by ext a; simp
/-
**Multiset.eq_sub_of_add_eq** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t u : Multiset α}, s + t = u → 
s = u - t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.add_sub_cancel_right`：∀ {α : Type u_1} [inst : DecidableEq α] {
s t : Multiset α}, s + t - t = s
-/
protected lemma eq_sub_of_add_eq (hstu : s + t = u) : s = u - t := by
  rw [← hstu, Multiset.add_sub_cancel_right]
/-
**Multiset.cons_sub_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：cons_sub_of_le (a : α) {s t : Multiset α} (h : t <= s) : a ::ₘ s - t = a :
:ₘ (s - t)
参数：a : α；h : t <= s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.singleton_add`：singleton_add (a : α) (s : Multiset α) : {a} + s
 = a ::ₘ s
· 使用定理 `Multiset.add_sub_assoc`：∀ {α : Type u_1} [inst : DecidableEq α] {s t u :
 Multiset α}, u ≤ t → s + t - u = s + (t - u)
-/
lemma cons_sub_of_le (a : α) {s t : Multiset α} (h : t ≤ s) : a ::ₘ s - t = a ::ₘ (s - t) := by
  rw [← singleton_add, ← singleton_add, Multiset.add_sub_assoc h]

@[simp]
/-
**Multiset.card_sub** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：card_sub {s t : Multiset α} (h : t <= s) : card (s - t) = card s - card t
参数：h : t <= s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_sub_of_add_eq`：∀ {a b c : ℕ}, c + b = a → c = a - b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.card_add`：card_add (s t : Multiset α) : card (s + t) = card s +
 card t
· 使用定理 `Multiset.sub_add_cancel`：∀ {α : Type u_1} [inst : DecidableEq α] {s t : 
Multiset α}, t ≤ s → s - t + t = s
-/
lemma card_sub {s t : Multiset α} (h : t ≤ s) : card (s - t) = card s - card t :=
  Nat.eq_sub_of_add_eq <| by rw [← card_add, Multiset.sub_add_cancel h]
/-
**Multiset.sub_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (s : Multiset α), s - {a} 
= s.erase a
参数：a : α；s : Multiset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.ext'`：ext' {s t : Multiset α} : (forall a, count a s = count a 
t) -> s = t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Multiset.count_sub`：count_sub (a : α) (s t : Multiset α) : count a (s - 
t) = count a s - count a t
· 使用定理 `Multiset.count_singleton`：count_singleton (a b : α) : count a ({b} : Mul
tiset α) = if a = b then 1 else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Multiset.count_erase_of_ne`：count_erase_of_ne {a b : α} (ab : a != b) (s
 : Multiset α) : count a (erase s b) = count a s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.count.congr_simp`：∀ {α : Type u_1} {inst : DecidableEq α} [inst
_1 : DecidableEq α] (a a_1 : α),   a = a_1 → ∀ (a_2 a_3 : Multiset α), a_2 = a_3
 → Multiset.cou…
· 使用定理 `Multiset.count_erase_self`：count_erase_self (a : α) (s : Multiset α) : c
ount a (erase s a) = count a s - 1
-/
@[simp] theorem sub_singleton (a : α) (s : Multiset α) : s - {a} = s.erase a := by
  ext
  simp only [count_sub, count_singleton]
  split <;> simp_all
/-
**Multiset.mem_sub** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_sub {a : α} {s t : Multiset α} : a in s - t ↔ t.count a < s.count a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.count_pos`：count_pos {a : α} {s : Multiset α} : 0 < count a s ↔
 a in s
· 使用引理 `Multiset.count_sub`：count_sub (a : α) (s t : Multiset α) : count a (s - 
t) = count a s - count a t
· 使用定理 `Nat.sub_pos_iff_lt`：∀ {n m : ℕ}, 0 < n - m ↔ m < n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_sub {a : α} {s t : Multiset α} :
    a ∈ s - t ↔ t.count a < s.count a := by
  rw [← count_pos, count_sub, Nat.sub_pos_iff_lt]

end sub

/-! ### Lift a relation to `Multiset`s -/


section Rel

variable {δ : Type*} {r : α → β → Prop} {p : γ → δ → Prop}

/-
**Multiset.Rel.add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Rel`。
形式化陈述：∀ {α : Type u_1} {β : Type v} {r : α → β → Prop} {s : Multiset α} {t : Mul
tiset β} {u : Multiset α} {v : Multiset β},   Multiset.Rel r s t → Multiset.Rel 
r u v → Multiset.Rel r (s + u) (t + v)
参数：s + u；t + v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.zero_add`：∀ {α : Type u_1} (s : Multiset α), 0 + s = s
· 使用定理 `Multiset.cons_add`：cons_add (a : α) (s t : Multiset α) : a ::ₘ s + t = a
 ::ₘ (s + t)
-/
theorem Rel.add {s t u v} (hst : Rel r s t) (huv : Rel r u v) : Rel r (s + u) (t + v) := by
  induction hst with
  | zero => simpa using huv
  | cons hab hst ih => simpa using ih.cons hab
/-
**Multiset.rel_add_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：rel_add_left {as₀ as₁} : forall {bs}, Rel r (as₀ + as₁) bs ↔ exists bs₀ bs
₁, Rel r as₀ bs₀ ∧ Rel r as₁ bs₁ ∧ bs = bs₀ + bs₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.zero_add`：∀ {α : Type u_1} (s : Multiset α), 0 + s = s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Multiset.cons_add`：cons_add (a : α) (s t : Multiset α) : a ::ₘ s + t = a
 ::ₘ (s + t)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem rel_add_left {as₀ as₁} :
    ∀ {bs}, Rel r (as₀ + as₁) bs ↔ ∃ bs₀ bs₁, Rel r as₀ bs₀ ∧ Rel r as₁ bs₁ ∧ bs = bs₀ + bs₁ :=
  @(Multiset.induction_on as₀ (by simp) fun a s ih bs ↦ by
      simp only [ih, cons_add, rel_cons_left]
      constructor
      · intro h
        rcases h with ⟨b, bs', hab, h, rfl⟩
        rcases h with ⟨bs₀, bs₁, h₀, h₁, rfl⟩
        exact ⟨b ::ₘ bs₀, bs₁, ⟨b, bs₀, hab, h₀, rfl⟩, h₁, by simp⟩
      · intro h
        rcases h with ⟨bs₀, bs₁, h, h₁, rfl⟩
        rcases h with ⟨b, bs, hab, h₀, rfl⟩
        exact ⟨b, bs + bs₁, hab, ⟨bs, bs₁, h₀, h₁, rfl⟩, by simp⟩)
/-
**Multiset.rel_add_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：rel_add_right {as bs₀ bs₁} : Rel r as (bs₀ + bs₁) ↔ exists as₀ as₁, Rel r 
as₀ bs₀ ∧ Rel r as₁ bs₁ ∧ as = as₀ + as₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.rel_flip`：rel_flip {s t} : Rel (flip r) s t ↔ Rel r t s
· 使用定理 `Multiset.rel_add_left`：rel_add_left {as₀ as₁} : forall {bs}, Rel r (as₀ 
+ as₁) bs ↔ exists bs₀ bs₁, Rel r as₀ bs₀ ∧ Rel r as₁ bs₁ ∧ bs = bs₀ + bs₁
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem rel_add_right {as bs₀ bs₁} :
    Rel r as (bs₀ + bs₁) ↔ ∃ as₀ as₁, Rel r as₀ bs₀ ∧ Rel r as₁ bs₁ ∧ as = as₀ + as₁ := by
  rw [← rel_flip, rel_add_left]; simp [rel_flip]

end Rel

section Nodup

@[simp]
/-
**Multiset.nodup_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：nodup_singleton : forall a : α, Nodup ({a} : Multiset α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.nodup_singleton`：nodup_singleton (a : α) : Nodup [a]
-/
theorem nodup_singleton : ∀ a : α, Nodup ({a} : Multiset α) :=
  List.nodup_singleton
/-
**Multiset.not_nodup_pair** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：not_nodup_pair : forall a : α, ¬Nodup (a ::ₘ a ::ₘ 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.not_nodup_pair`：not_nodup_pair (a : α) : ¬Nodup [a, a]
-/
theorem not_nodup_pair : ∀ a : α, ¬Nodup (a ::ₘ a ::ₘ 0) :=
  List.not_nodup_pair
/-
**Multiset.Nodup.erase** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (a : α) {l : Multiset α}, l.Nodup 
→ (l.erase a).Nodup
参数：a : α；l.erase a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.nodup_of_le`：nodup_of_le {s t : Multiset α} (h : s <= t) : Nodu
p t -> Nodup s
· 使用定理 `Multiset.erase_le`：erase_le (a : α) (s : Multiset α) : s.erase a <= s
-/
theorem Nodup.erase [DecidableEq α] (a : α) {l} : Nodup l → Nodup (l.erase a) :=
  nodup_of_le (erase_le _ _)
/-
**Multiset.mem_sub_of_nodup** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_sub_of_nodup [DecidableEq α] {a : α} {s t : Multiset α} (d : Nodup s) 
: a in s - t ↔ a in s ∧ a ∉ t
参数：d : Nodup s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_of_le`：mem_of_le (h : s <= t) : a in s -> a in t
· 使用定理 `Multiset.sub_le_self`：∀ {α : Type u_1} [inst : DecidableEq α] (s t : Mul
tiset α), s - t ≤ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.count_eq_zero`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Mul
tiset α} {a : α}, Multiset.count a s = 0 ↔ a ∉ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Multiset.count_sub`：count_sub (a : α) (s t : Multiset α) : count a (s - 
t) = count a s - count a t
· 使用定理 `Nat.sub_eq_zero_iff_le`：∀ {n m : ℕ}, n - m = 0 ↔ n ≤ m
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Multiset.nodup_iff_count_le_one`：nodup_iff_count_le_one [DecidableEq α] 
{s : Multiset α} : Nodup s ↔ forall a, count a s <= 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.count_pos`：count_pos {a : α} {s : Multiset α} : 0 < count a s ↔
 a in s
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Multiset.mem_add`：mem_add {a : α} {s t : Multiset α} : a in s + t ↔ a in
 s ∨ a in t
· 使用定理 `Multiset.le_sub_add`：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Mult
iset α}, s ≤ s - t + t
-/
theorem mem_sub_of_nodup [DecidableEq α] {a : α} {s t : Multiset α} (d : Nodup s) :
    a ∈ s - t ↔ a ∈ s ∧ a ∉ t :=
  ⟨fun h =>
    ⟨mem_of_le (Multiset.sub_le_self ..) h, fun h' => by
      refine count_eq_zero.1 ?_ h
      rw [count_sub a s t, Nat.sub_eq_zero_iff_le]
      exact le_trans (nodup_iff_count_le_one.1 d _) (count_pos.2 h')⟩,
    fun ⟨h₁, h₂⟩ => Or.resolve_right (mem_add.1 <| mem_of_le Multiset.le_sub_add h₁) h₂⟩

end Nodup

end Multiset

