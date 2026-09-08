/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Rudy Peterson
-/
module

public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Data.Set.Function
public import Mathlib.Order.Hom.Basic

/-!
# Filtering multisets by a predicate

## Main definitions

* `Multiset.filter`: `filter p s` is the multiset of elements in `s` that satisfy `p`.
* `Multiset.filterMap`: `filterMap f s` is the multiset of `b`s where `some b ∈ map f s`.
-/

@[expose] public section

-- No algebra should be required
assert_not_exists Monoid

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

/-! ### `Multiset.filter` -/


section

variable (p : α → Prop) [DecidablePred p]

/-- `Filter p s` returns the elements in `s` (with the same multiplicities)
  which satisfy `p`, and removes the rest. -/
/-
**Multiset.filter** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：filter (s : Multiset α) : Multiset α
参数：s : Multiset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Filter p s` returns the elements in `s` (with the same multiplicities)
  which satisfy `p`, and removes the rest.
-/
def filter (s : Multiset α) : Multiset α :=
  Quot.liftOn s (fun l => (List.filter p l : Multiset α)) fun _l₁ _l₂ h => Quot.sound <| h.filter p
/-
**Multiset.filter_coe** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred p] (l : List α),   M
ultiset.filter p ↑l = ↑(List.filter (fun b => decide (p b)) l)
参数：p : α → Prop；l : List α；List.filter (fun b => decide (p b)) l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma filter_coe (l : List α) : filter p l = l.filter p := rfl

@[simp]
/-
**Multiset.filter_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filter_zero : filter p 0 = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_zero : filter p 0 = 0 :=
  rfl

@[congr]
/-
**Multiset.filter_congr** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filter_congr {p q : α -> Prop} [DecidablePred p] [DecidablePred q] {s : Mu
ltiset α} : (forall x in s, p x ↔ q x) -> filter p s = filter q s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.filter_congr`：∀ {α : Type u_1} {p q : α → Bool} {l : List α}, (∀ x 
∈ l, p x = q x) → List.filter p l = List.filter q l
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem filter_congr {p q : α → Prop} [DecidablePred p] [DecidablePred q] {s : Multiset α} :
    (∀ x ∈ s, p x ↔ q x) → filter p s = filter q s :=
  Quot.inductionOn s fun _l h => congr_arg ofList <| List.filter_congr <| by simpa using h

@[simp]
/-
**Multiset.filter_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filter_add (s t : Multiset α) : filter p (s + t) = filter p s + filter p t
参数：s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.filter_append`：∀ {α : Type u_1} {p : α → Bool} (l₁ l₂ : List α), Li
st.filter p (l₁ ++ l₂) = List.filter p l₁ ++ List.filter p l₂
-/
theorem filter_add (s t : Multiset α) : filter p (s + t) = filter p s + filter p t :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ => congr_arg ofList <| filter_append _ _

@[simp]
/-
**Multiset.filter_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filter_le (s : Multiset α) : filter p s <= s
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.Sublist.subperm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ →
 l₁.Subperm l₂
· 使用定理 `List.filter_sublist`：∀ {α : Type u_1} {p : α → Bool} {l : List α}, (List
.filter p l).Sublist l
-/
theorem filter_le (s : Multiset α) : filter p s ≤ s :=
  Quot.inductionOn s fun _l => filter_sublist.subperm

@[simp]
/-
**Multiset.filter_subset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filter_subset (s : Multiset α) : filter p s subseteq s
参数：s : Multiset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.subset_of_le`：subset_of_le : s <= t -> s subseteq t
· 使用定理 `Multiset.filter_le`：filter_le (s : Multiset α) : filter p s <= s
-/
theorem filter_subset (s : Multiset α) : filter p s ⊆ s :=
  subset_of_le <| filter_le _ _

@[gcongr]
/-
**Multiset.filter_le_filter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filter_le_filter {s t} (h : s <= t) : filter p s <= filter p t
参数：h : s <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.leInductionOn`：leInductionOn {C : Multiset α -> Multiset α -> P
rop} {s t : Multiset α} (h : s <= t) (H : forall {l₁ l₂ : List α}, l₁ <+ l₂ -> C
 l₁ l₂) : C …
· 使用定理 `List.Sublist.subperm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ →
 l₁.Subperm l₂
· 使用定理 `List.Sublist.filter`：∀ {α : Type u_1} (p : α → Bool) {l₁ l₂ : List α}, l
₁.Sublist l₂ → (List.filter p l₁).Sublist (List.filter p l₂)
-/
theorem filter_le_filter {s t} (h : s ≤ t) : filter p s ≤ filter p t :=
  leInductionOn h fun h => (h.filter (p ·)).subperm
/-
**Multiset.monotone_filter_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：monotone_filter_left : Monotone (filter p)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.filter_le_filter`：filter_le_filter {s t} (h : s <= t) : filter 
p s <= filter p t
-/
theorem monotone_filter_left : Monotone (filter p) := fun _s _t => filter_le_filter p
/-
**Multiset.monotone_filter_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：monotone_filter_right (s : Multiset α) ⦃p q : α -> Prop⦄ [DecidablePred p]
 [DecidablePred q] (h : forall b, p b -> q b) : s.filter p <= s.filter q
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `List.Sublist.subperm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ →
 l₁.Subperm l₂
· 使用定理 `List.monotone_filter_right`：monotone_filter_right (l : List α) ⦃p q : α 
-> Bool⦄ (h : forall a, p a -> q a) : l.filter p <+ l.filter q
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
-/
theorem monotone_filter_right (s : Multiset α) ⦃p q : α → Prop⦄ [DecidablePred p] [DecidablePred q]
    (h : ∀ b, p b → q b) :
    s.filter p ≤ s.filter q :=
  Quotient.inductionOn s fun l => (l.monotone_filter_right <| by simpa using h).subperm

variable {p}

@[simp]
/-
**Multiset.filter_cons_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filter_cons_of_pos {a : α} (s) : p a -> filter p (a ::ₘ s) = a ::ₘ filter 
p s
参数：s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.filter_cons_of_pos`：∀ {α : Type u_1} {p : α → Bool} {a : α} {l : Li
st α}, p a = true → List.filter p (a :: l) = a :: List.filter p l
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
-/
theorem filter_cons_of_pos {a : α} (s) : p a → filter p (a ::ₘ s) = a ::ₘ filter p s :=
  Quot.inductionOn s fun _ h => congr_arg ofList <| List.filter_cons_of_pos <| by simpa using h

@[simp]
/-
**Multiset.filter_cons_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filter_cons_of_neg {a : α} (s) : ¬p a -> filter p (a ::ₘ s) = filter p s
参数：s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.filter_cons_of_neg`：∀ {α : Type u_1} {p : α → Bool} {a : α} {l : Li
st α}, ¬p a = true → List.filter p (a :: l) = List.filter p l
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
-/
theorem filter_cons_of_neg {a : α} (s) : ¬p a → filter p (a ::ₘ s) = filter p s :=
  Quot.inductionOn s fun _ h => congr_arg ofList <| List.filter_cons_of_neg <| by simpa using h

@[simp]
/-
**Multiset.mem_filter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_filter {a : α} {s} : a in filter p s ↔ a in s ∧ p a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_filter {a : α} {s} : a ∈ filter p s ↔ a ∈ s ∧ p a :=
  Quot.inductionOn s fun _l => by simp
/-
**Multiset.of_mem_filter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：of_mem_filter {a : α} {s} (h : a in filter p s) : p a
参数：h : a in filter p s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_filter`：mem_filter {a : α} {s} : a in filter p s ↔ a in s ∧
 p a
-/
theorem of_mem_filter {a : α} {s} (h : a ∈ filter p s) : p a :=
  (mem_filter.1 h).2
/-
**Multiset.mem_of_mem_filter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_of_mem_filter {a : α} {s} (h : a in filter p s) : a in s
参数：h : a in filter p s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_filter`：mem_filter {a : α} {s} : a in filter p s ↔ a in s ∧
 p a
-/
theorem mem_of_mem_filter {a : α} {s} (h : a ∈ filter p s) : a ∈ s :=
  (mem_filter.1 h).1
/-
**Multiset.mem_filter_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_filter_of_mem {a : α} {l} (m : a in l) (h : p a) : a in filter p l
参数：m : a in l；h : p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.mem_filter`：mem_filter {a : α} {s} : a in filter p s ↔ a in s ∧
 p a
-/
theorem mem_filter_of_mem {a : α} {l} (m : a ∈ l) (h : p a) : a ∈ filter p l :=
  mem_filter.2 ⟨m, h⟩

@[simp]
/-
**Multiset.filter_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filter_eq_self {s} : filter p s = s ↔ forall a in s, p a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `List.Sublist.eq_of_length`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist
 l₂ → l₁.length = l₂.length → l₁ = l₂
· 使用定理 `List.filter_sublist`：∀ {α : Type u_1} {p : α → Bool} {l : List α}, (List
.filter p l).Sublist l
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem filter_eq_self {s} : filter p s = s ↔ ∀ a ∈ s, p a :=
  Quot.inductionOn s fun _l =>
    Iff.trans ⟨fun h => filter_sublist.eq_of_length (congr_arg card h),
      congr_arg ofList⟩ <| by simp

@[simp]
/-
**Multiset.filter_eq_nil** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filter_eq_nil {s} : filter p s = 0 ↔ forall a in s, ¬p a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `List.eq_nil_of_length_eq_zero`：∀ {α : Type u_1} {l : List α}, l.length =
 0 → l = []
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem filter_eq_nil {s} : filter p s = 0 ↔ ∀ a ∈ s, ¬p a :=
  Quot.inductionOn s fun _l =>
    Iff.trans ⟨fun h => eq_nil_of_length_eq_zero (congr_arg card h), congr_arg ofList⟩ (by simp)

@[simp]
/-
**Multiset.filter_true** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：filter_true (s : Multiset α) : s.filter (fun _ => True) = s
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma filter_true (s : Multiset α) : s.filter (fun _ ↦ True) = s := by simp

@[simp]
/-
**Multiset.filter_false** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：filter_false (s : Multiset α) : s.filter (fun _ => False) = 0
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma filter_false (s : Multiset α) : s.filter (fun _ ↦ False) = 0 := by simp
/-
**Multiset.le_filter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：le_filter {s t} : s <= filter p t ↔ s <= t ∧ forall a in s, p a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Multiset.filter_le`：filter_le (s : Multiset α) : filter p s <= s
· 使用定理 `Multiset.of_mem_filter`：of_mem_filter {a : α} {s} (h : a in filter p s) 
: p a
· 使用定理 `Multiset.mem_of_le`：mem_of_le (h : s <= t) : a in s -> a in t
· 使用定理 `Multiset.filter_le_filter`：filter_le_filter {s t} (h : s <= t) : filter 
p s <= filter p t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.filter_eq_self`：filter_eq_self {s} : filter p s = s ↔ forall a 
in s, p a
-/
theorem le_filter {s t} : s ≤ filter p t ↔ s ≤ t ∧ ∀ a ∈ s, p a :=
  ⟨fun h => ⟨le_trans h (filter_le _ _), fun _a m => of_mem_filter (mem_of_le h m)⟩, fun ⟨h, al⟩ =>
    filter_eq_self.2 al ▸ filter_le_filter p h⟩
/-
**Multiset.filter_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filter_cons {a : α} (s : Multiset α) : filter p (a ::ₘ s) = (if p a then {
a} else 0) + filter p s
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Multiset.filter_cons_of_pos`：filter_cons_of_pos {a : α} (s) : p a -> fil
ter p (a ::ₘ s) = a ::ₘ filter p s
· 使用定理 `Multiset.singleton_add`：singleton_add (a : α) (s : Multiset α) : {a} + s
 = a ::ₘ s
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Multiset.filter_cons_of_neg`：filter_cons_of_neg {a : α} (s) : ¬p a -> fi
lter p (a ::ₘ s) = filter p s
· 使用定理 `Multiset.zero_add`：∀ {α : Type u_1} (s : Multiset α), 0 + s = s
-/
theorem filter_cons {a : α} (s : Multiset α) :
    filter p (a ::ₘ s) = (if p a then {a} else 0) + filter p s := by
  split_ifs with h
  · rw [filter_cons_of_pos _ h, singleton_add]
  · rw [filter_cons_of_neg _ h, Multiset.zero_add]
/-
**Multiset.filter_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filter_singleton {a : α} (p : α -> Prop) [DecidablePred p] : filter p {a} 
= if p a then {a} else ∅
参数：p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.filter_cons`：filter_cons {a : α} (s : Multiset α) : filter p (a
 ::ₘ s) = (if p a then {a} else 0) + filter p s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Multiset.add_zero`：∀ {α : Type u_1} (s : Multiset α), s + 0 = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem filter_singleton {a : α} (p : α → Prop) [DecidablePred p] :
    filter p {a} = if p a then {a} else ∅ := by
  simp only [singleton, filter_cons, filter_zero, Multiset.add_zero, empty_eq_zero]

variable (p)

@[simp]
/-
**Multiset.filter_filter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filter_filter (q) [DecidablePred q] (s : Multiset α) : filter p (filter q 
s) = filter (fun a => p a ∧ q a) s
参数：q；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.filter_filter`：∀ {α : Type u_1} {p q : α → Bool} {l : List α}, List
.filter p (List.filter q l) = List.filter (fun a => p a && q a) l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Bool.decide_and`：∀ (p q : Prop) [dpq : Decidable (p ∧ q)] [dp : Decidabl
e p] [dq : Decidable q], decide (p ∧ q) = (decide p && decide q)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem filter_filter (q) [DecidablePred q] (s : Multiset α) :
    filter p (filter q s) = filter (fun a => p a ∧ q a) s :=
  Quot.inductionOn s fun l => by simp
/-
**Multiset.filter_comm** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：filter_comm (q) [DecidablePred q] (s : Multiset α) : filter p (filter q s)
 = filter q (filter p s)
参数：q；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.filter_filter`：filter_filter (q) [DecidablePred q] (s : Multise
t α) : filter p (filter q s) = filter (fun a => p a ∧ q a) s
· 使用定理 `Multiset.filter_congr`：filter_congr {p q : α -> Prop} [DecidablePred p] 
[DecidablePred q] {s : Multiset α} : (forall x in s, p x ↔ q x) -> filter p s = 
filter q s
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma filter_comm (q) [DecidablePred q] (s : Multiset α) :
    filter p (filter q s) = filter q (filter p s) := by simp [and_comm]
/-
**Multiset.filter_add_filter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filter_add_filter (q) [DecidablePred q] (s : Multiset α) : filter p s + fi
lter q s = filter (fun a => p a ∨ q a) s + filter (fun a => p a ∧ q a) s
参数：q；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.filter_cons_of_pos`：filter_cons_of_pos {a : α} (s) : p a -> fil
ter p (a ::ₘ s) = a ::ₘ filter p s
· 使用定理 `Multiset.add_cons`：add_cons (a : α) (s t : Multiset α) : s + a ::ₘ t = a
 ::ₘ (s + t)
· 使用定理 `Multiset.cons_add`：cons_add (a : α) (s t : Multiset α) : a ::ₘ s + t = a
 ::ₘ (s + t)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.filter_cons_of_neg`：filter_cons_of_neg {a : α} (s) : ¬p a -> fi
lter p (a ::ₘ s) = filter p s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem filter_add_filter (q) [DecidablePred q] (s : Multiset α) :
    filter p s + filter q s = filter (fun a => p a ∨ q a) s + filter (fun a => p a ∧ q a) s :=
  Multiset.induction_on s rfl fun a s IH => by by_cases p a <;> by_cases q a <;> simp [*]
/-
**Multiset.filter_add_not** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filter_add_not (s : Multiset α) : filter p s + filter (fun a => ¬p a) s = 
s
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.filter_add_filter`：filter_add_filter (q) [DecidablePred q] (s :
 Multiset α) : filter p s + filter q s = filter (fun a => p a ∨ q a) s + filter 
(fun a => p a ∧ …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.filter_eq_self`：filter_eq_self {s} : filter p s = s ↔ forall a 
in s, p a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Multiset.filter_eq_nil`：filter_eq_nil {s} : filter p s = 0 ↔ forall a in
 s, ¬p a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.add_zero`：∀ {α : Type u_1} (s : Multiset α), s + 0 = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem filter_add_not (s : Multiset α) : filter p s + filter (fun a => ¬p a) s = s := by
  rw [filter_add_filter, filter_eq_self.2, filter_eq_nil.2]
  · simp only [Multiset.add_zero]
  · simp [-Bool.not_eq_true, -not_and]
  · simp only [implies_true, Decidable.em]
/-
**Multiset.filter_map** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filter_map (f : β -> α) (s : Multiset β) : filter p (map f s) = map f (fil
ter (p ∘ f) s)
参数：f : β -> α；s : Multiset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.filter_map`：∀ {β : Type u_1} {α : Type u_2} {f : β → α} {p : α → Bo
ol} {l : List β},   List.filter p (List.map f l) = List.map f (List.filter (p ∘ 
f) l)
· 使用定理 `List.Perm.refl`：∀ {α : Type u_1} (l : List α), l.Perm l
-/
theorem filter_map (f : β → α) (s : Multiset β) : filter p (map f s) = map f (filter (p ∘ f) s) :=
  Quot.inductionOn s fun l => by simp [List.filter_map]; rfl

-- TODO: rename to `map_filter` when the deprecated alias above is removed.
/-
**Multiset.map_filter'** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：map_filter' {f : α -> β} (hf : Injective f) (s : Multiset α) [DecidablePre
d fun b => exists a, p a ∧ f a = b] : (s.filter p).map f = (s.map f).filter fun 
b => exists a, p a ∧ f a = b
参数：hf : Injective f；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.filter_map`：filter_map (f : β -> α) (s : Multiset β) : filter p
 (map f s) = map f (filter (p ∘ f) s)
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.filter_congr`：filter_congr {p q : α -> Prop} [DecidablePred p] 
[DecidablePred q] {s : Multiset α} : (forall x in s, p x ↔ q x) -> filter p s = 
filter q s
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_filter' {f : α → β} (hf : Injective f) (s : Multiset α)
    [DecidablePred fun b => ∃ a, p a ∧ f a = b] :
    (s.filter p).map f = (s.map f).filter fun b => ∃ a, p a ∧ f a = b := by
  simp [filter_map, hf.eq_iff]
/-
**Multiset.card_filter_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：card_filter_le_iff (s : Multiset α) (P : α -> Prop) [DecidablePred P] (n :
 Nat) : card (s.filter P) <= n ↔ forall s' <= s, n < card s' -> exists a in s', 
¬ P a
参数：s : Multiset α；P : α -> Prop；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Multiset.card_le_card`：card_le_card {s t : Multiset α} (h : s <= t) : ca
rd s <= card t
· 使用定理 `Multiset.monotone_filter_left`：monotone_filter_left : Monotone (filter p
)
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.filter_eq_self`：filter_eq_self {s} : filter p s = s ↔ forall a 
in s, p a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Multiset.filter_le`：filter_le (s : Multiset α) : filter p s <= s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_filter`：mem_filter {a : α} {s} : a in filter p s ↔ a in s ∧
 p a
-/
lemma card_filter_le_iff (s : Multiset α) (P : α → Prop) [DecidablePred P] (n : ℕ) :
    card (s.filter P) ≤ n ↔ ∀ s' ≤ s, n < card s' → ∃ a ∈ s', ¬ P a := by
  fconstructor
  · intro H s' hs' s'_card
    by_contra! rid
    have card := card_le_card (monotone_filter_left P hs') |>.trans H
    exact s'_card.not_ge (filter_eq_self.mpr rid ▸ card)
  · contrapose!
    exact fun H ↦ ⟨s.filter P, filter_le _ _, H, fun a ha ↦ (mem_filter.mp ha).2⟩

/-! ### Simultaneously filter and map elements of a multiset -/


/-- `filterMap f s` is a combination filter/map operation on `s`.
  The function `f : α → Option β` is applied to each element of `s`;
  if `f a` is `some b` then `b` is added to the result, otherwise
  `a` is removed from the resulting multiset. -/
/-
**Multiset.filterMap** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：filterMap (f : α -> Option β) (s : Multiset α) : Multiset β
参数：f : α -> Option β；s : Multiset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`filterMap f s` is a combination filter/map operation on `s`.
  The function `f : α → Option β` is applied to each element of `s`;
  if `f a` is `some b` then `b` is added to the result, otherwise
  `a` is removed from the resulting multiset.
-/
def filterMap (f : α → Option β) (s : Multiset α) : Multiset β :=
  Quot.liftOn s (fun l => (List.filterMap f l : Multiset β))
    fun _l₁ _l₂ h => Quot.sound <| h.filterMap f

@[simp, norm_cast]
/-
**Multiset.filterMap_coe** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：filterMap_coe (f : α -> Option β) (l : List α) : filterMap f l = l.filterM
ap f
参数：f : α -> Option β；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma filterMap_coe (f : α → Option β) (l : List α) : filterMap f l = l.filterMap f := rfl

@[simp]
/-
**Multiset.filterMap_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filterMap_zero (f : α -> Option β) : filterMap f 0 = 0
参数：f : α -> Option β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filterMap_zero (f : α → Option β) : filterMap f 0 = 0 :=
  rfl

@[simp]
/-
**Multiset.filterMap_cons_none** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filterMap_cons_none {f : α -> Option β} (a : α) (s : Multiset α) (h : f a 
= none) : filterMap f (a ::ₘ s) = filterMap f s
参数：a : α；s : Multiset α；h : f a = none。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.filterMap_cons_none`：∀ {α : Type u_1} {β : Type u_2} {f : α → Optio
n β} {a : α} {l : List α},   f a = none → List.filterMap f (a :: l) = List.filte
rMap f l
-/
theorem filterMap_cons_none {f : α → Option β} (a : α) (s : Multiset α) (h : f a = none) :
    filterMap f (a ::ₘ s) = filterMap f s :=
  Quot.inductionOn s fun _ => congr_arg ofList <| List.filterMap_cons_none h

@[simp]
/-
**Multiset.filterMap_cons_some** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filterMap_cons_some (f : α -> Option β) (a : α) (s : Multiset α) {b : β} (
h : f a = some b) : filterMap f (a ::ₘ s) = b ::ₘ filterMap f s
参数：f : α -> Option β；a : α；s : Multiset α；h : f a = some b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.filterMap_cons_some`：∀ {α : Type u_1} {β : Type u_2} {f : α → Optio
n β} {a : α} {l : List α} {b : β},   f a = some b → List.filterMap f (a :: l) = 
b :: List.filt…
-/
theorem filterMap_cons_some (f : α → Option β) (a : α) (s : Multiset α) {b : β}
    (h : f a = some b) : filterMap f (a ::ₘ s) = b ::ₘ filterMap f s :=
  Quot.inductionOn s fun _ => congr_arg ofList <| List.filterMap_cons_some h
/-
**Multiset.filterMap_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filterMap_cons (f : α -> Option β) (a : α) (s : Multiset α) : filterMap f 
(a ::ₘ s) = ((f a).map singleton).getD 0 + filterMap f s
参数：f : α -> Option β；a : α；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.filterMap_cons_none`：filterMap_cons_none {f : α -> Option β} (a
 : α) (s : Multiset α) (h : f a = none) : filterMap f (a ::ₘ s) = filterMap f s
· 使用定理 `Multiset.zero_add`：∀ {α : Type u_1} (s : Multiset α), 0 + s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.filterMap_cons_some`：filterMap_cons_some (f : α -> Option β) (a
 : α) (s : Multiset α) {b : β} (h : f a = some b) : filterMap f (a ::ₘ s) = b ::
ₘ filterMap f s
-/
theorem filterMap_cons (f : α → Option β) (a : α) (s : Multiset α) :
    filterMap f (a ::ₘ s) = ((f a).map singleton).getD 0 + filterMap f s := by
  cases h : f a with
  | none => simp [filterMap_cons_none a s h]
  | some b => simp [filterMap_cons_some f a s h]

@[simp]
/-
**Multiset.filterMap_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filterMap_add (f : α -> Option β) (s t : Multiset α) : filterMap f (s + t)
 = filterMap f s + filterMap f t
参数：f : α -> Option β；s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.filterMap_append`：∀ {α : Type u_1} {β : Type u_2} {l l' : List α} {
f : α → Option β},   List.filterMap f (l ++ l') = List.filterMap f l ++ List.fil
terMap f l'
-/
theorem filterMap_add (f : α → Option β) (s t : Multiset α) :
    filterMap f (s + t) = filterMap f s + filterMap f t :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ => congr_arg ofList <| filterMap_append
/-
**Multiset.filterMap_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filterMap_eq_map (f : α -> β) : filterMap (some ∘ f) = map f
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `List.filterMap_eq_map`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, List
.filterMap (some ∘ f) = List.map f
-/
theorem filterMap_eq_map (f : α → β) : filterMap (some ∘ f) = map f :=
  funext fun s =>
    Quot.inductionOn s fun l => congr_arg ofList <| congr_fun List.filterMap_eq_map l
/-
**Multiset.filterMap_eq_filter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filterMap_eq_filter : filterMap (Option.guard p) = filter p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.filterMap_eq_filter`：∀ {α : Type u_1} {p : α → Bool}, List.filterMa
p (Option.guard fun x => p x) = List.filter p
-/
theorem filterMap_eq_filter : filterMap (Option.guard p) = filter p :=
  funext fun s =>
    Quot.inductionOn s fun l => congr_arg ofList <| by
      rw [← List.filterMap_eq_filter]
/-
**Multiset.filterMap_filterMap** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filterMap_filterMap (f : α -> Option β) (g : β -> Option γ) (s : Multiset 
α) : filterMap g (filterMap f s) = filterMap (fun x => (f x).bind g) s
参数：f : α -> Option β；g : β -> Option γ；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.filterMap_filterMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3}
 {f : α → Option β} {g : β → Option γ} {l : List α},   List.filterMap g (List.fi
lterMap f l) =…
-/
theorem filterMap_filterMap (f : α → Option β) (g : β → Option γ) (s : Multiset α) :
    filterMap g (filterMap f s) = filterMap (fun x => (f x).bind g) s :=
  Quot.inductionOn s fun _ => congr_arg ofList List.filterMap_filterMap
/-
**Multiset.map_filterMap** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_filterMap (f : α -> Option β) (g : β -> γ) (s : Multiset α) : map g (f
ilterMap f s) = filterMap (fun x => (f x).map g) s
参数：f : α -> Option β；g : β -> γ；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.map_filterMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : 
α → Option β} {g : β → γ} {l : List α},   List.map g (List.filterMap f l) = List
.filterM…
-/
theorem map_filterMap (f : α → Option β) (g : β → γ) (s : Multiset α) :
    map g (filterMap f s) = filterMap (fun x => (f x).map g) s :=
  Quot.inductionOn s fun _ => congr_arg ofList List.map_filterMap
/-
**Multiset.filterMap_map** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filterMap_map (f : α -> β) (g : β -> Option γ) (s : Multiset α) : filterMa
p g (map f s) = filterMap (g ∘ f) s
参数：f : α -> β；g : β -> Option γ；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.filterMap_map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : 
α → β} {g : β → Option γ} {l : List α},   List.filterMap g (List.map f l) = List
.filterM…
-/
theorem filterMap_map (f : α → β) (g : β → Option γ) (s : Multiset α) :
    filterMap g (map f s) = filterMap (g ∘ f) s :=
  Quot.inductionOn s fun _ => congr_arg ofList List.filterMap_map
/-
**Multiset.filter_filterMap** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filter_filterMap (f : α -> Option β) (p : β -> Prop) [DecidablePred p] (s 
: Multiset α) : filter p (filterMap f s) = filterMap (fun x => (f x).filter p) s
参数：f : α -> Option β；p : β -> Prop；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.filter_filterMap`：∀ {α : Type u_1} {β : Type u_2} {f : α → Option β
} {p : β → Bool} {l : List α},   List.filter p (List.filterMap f l) = List.filte
rMap (fun x…
-/
theorem filter_filterMap (f : α → Option β) (p : β → Prop) [DecidablePred p] (s : Multiset α) :
    filter p (filterMap f s) = filterMap (fun x => (f x).filter p) s :=
  Quot.inductionOn s fun _ => congr_arg ofList List.filter_filterMap
/-
**Multiset.filterMap_filter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filterMap_filter (f : α -> Option β) (s : Multiset α) : filterMap f (filte
r p s) = filterMap (fun x => if p x then f x else none) s
参数：f : α -> Option β；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.filterMap_congr`：filterMap_congr {f g : α -> Option β} {l : List α}
 (h : forall x in l, f x = g x) : l.filterMap f = l.filterMap g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `List.filterMap_filter`：∀ {α : Type u_1} {β : Type u_2} {p : α → Bool} {f
 : α → Option β} {l : List α},   List.filterMap f (List.filter p l) = List.filte
rMap (fun x…
-/
theorem filterMap_filter (f : α → Option β) (s : Multiset α) :
    filterMap f (filter p s) = filterMap (fun x => if p x then f x else none) s :=
  Quot.inductionOn s fun l => congr_arg ofList <| by
    simpa using List.filterMap_filter (f := f) (p := p)

@[simp]
/-
**Multiset.filterMap_some** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filterMap_some (s : Multiset α) : filterMap some s = s
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.filterMap_some`：∀ {α : Type u_1} {l : List α}, List.filterMap some 
l = l
-/
theorem filterMap_some (s : Multiset α) : filterMap some s = s :=
  Quot.inductionOn s fun _ => congr_arg ofList List.filterMap_some

@[simp]
/-
**Multiset.mem_filterMap** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_filterMap (f : α -> Option β) (s : Multiset α) {b : β} : b in filterMa
p f s ↔ exists a, a in s ∧ f a = some b
参数：f : α -> Option β；s : Multiset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.mem_filterMap`：∀ {α : Type u_1} {β : Type u_2} {f : α → Option β} {
l : List α} {b : β}, b ∈ List.filterMap f l ↔ ∃ a ∈ l, f a = some b
-/
theorem mem_filterMap (f : α → Option β) (s : Multiset α) {b : β} :
    b ∈ filterMap f s ↔ ∃ a, a ∈ s ∧ f a = some b :=
  Quot.inductionOn s fun _ => List.mem_filterMap
/-
**Multiset.map_filterMap_of_inv** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_filterMap_of_inv (f : α -> Option β) (g : β -> α) (H : forall x : α, (
f x).map g = some x) (s : Multiset α) : map g (filterMap f s) = s
参数：f : α -> Option β；g : β -> α；H : forall x : α, (f x).map g = some x；s : Multi
set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.map_filterMap_of_inv`：∀ {α : Type u_1} {β : Type u_2} {f : α → Opti
on β} {g : β → α},   (∀ (x : α), Option.map g (f x) = some x) → ∀ {l : List α}, 
List.map g (Lis…
-/
theorem map_filterMap_of_inv (f : α → Option β) (g : β → α) (H : ∀ x : α, (f x).map g = some x)
    (s : Multiset α) : map g (filterMap f s) = s :=
  Quot.inductionOn s fun _ => congr_arg ofList <| List.map_filterMap_of_inv H

@[gcongr]
/-
**Multiset.filterMap_le_filterMap** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filterMap_le_filterMap (f : α -> Option β) {s t : Multiset α} (h : s <= t)
 : filterMap f s <= filterMap f t
参数：f : α -> Option β；h : s <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.leInductionOn`：leInductionOn {C : Multiset α -> Multiset α -> P
rop} {s t : Multiset α} (h : s <= t) (H : forall {l₁ l₂ : List α}, l₁ <+ l₂ -> C
 l₁ l₂) : C …
· 使用定理 `List.Sublist.subperm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ →
 l₁.Subperm l₂
· 使用定理 `List.Sublist.filterMap`：∀ {α : Type u_1} {β : Type u_2} {l₁ l₂ : List α}
 (f : α → Option β),   l₁.Sublist l₂ → (List.filterMap f l₁).Sublist (List.filte
rMap f l₂)
-/
theorem filterMap_le_filterMap (f : α → Option β) {s t : Multiset α} (h : s ≤ t) :
    filterMap f s ≤ filterMap f t :=
  leInductionOn h fun h => (h.filterMap _).subperm
/-
**Multiset.map_filter_eq_filterMap** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_filter_eq_filterMap (f : α -> β) (p : α -> Prop) [DecidablePred p] (s 
: Multiset α) : map f (filter p s) = filterMap (fun a => if p a then .some (f a)
 else .none) s
参数：f : α -> β；p : α -> Prop；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction`：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀
 (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.filter_cons`：filter_cons {a : α} (s : Multiset α) : filter p (a
 ::ₘ s) = (if p a then {a} else 0) + filter p s
· 使用定理 `Multiset.map_add`：map_add (f : α -> β) (s t) : map f (s + t) = map f s +
 map f t
· 使用定理 `Multiset.filterMap_cons`：filterMap_cons (f : α -> Option β) (a : α) (s :
 Multiset α) : filterMap f (a ::ₘ s) = ((f a).map singleton).getD 0 + filterMap 
f s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Option.map_if`：∀ {α : Type u_1} {β : Type u_2} {c : Prop} {a : α} {f : α
 → β} {x : Decidable c},   Option.map f (if c then some a else none) = if c then
 so…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem map_filter_eq_filterMap (f : α → β) (p : α → Prop) [DecidablePred p] (s : Multiset α) :
    map f (filter p s) = filterMap (fun a => if p a then .some (f a) else .none) s := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [filter_cons, map_add, ih, filterMap_cons, Option.map_if]; clear ih; congr
    split_ifs <;> simp

/-! ### countP -/

/-
**Multiset.countP_eq_card_filter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：countP_eq_card_filter (s) : countP p s = card (filter p s)
参数：s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.countP_eq_length_filter`：∀ {α : Type u_1} {p : α → Bool} {l : List 
α}, List.countP p l = (List.filter p l).length

--- 原说明 ---
### countP
-/
theorem countP_eq_card_filter (s) : countP p s = card (filter p s) :=
  Quot.inductionOn s fun l => l.countP_eq_length_filter (p := (p ·))

@[simp]
/-
**Multiset.countP_filter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：countP_filter (q) [DecidablePred q] (s : Multiset α) : countP p (filter q 
s) = countP (fun a => p a ∧ q a) s
参数：q；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.countP_eq_card_filter`：countP_eq_card_filter (s) : countP p s =
 card (filter p s)
· 使用定理 `Multiset.filter_filter`：filter_filter (q) [DecidablePred q] (s : Multise
t α) : filter p (filter q s) = filter (fun a => p a ∧ q a) s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem countP_filter (q) [DecidablePred q] (s : Multiset α) :
    countP p (filter q s) = countP (fun a => p a ∧ q a) s := by simp [countP_eq_card_filter]
/-
**Multiset.countP_eq_countP_filter_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：countP_eq_countP_filter_add (s) (p q : α -> Prop) [DecidablePred p] [Decid
ablePred q] : countP p s = (filter q s).countP p + (filter (fun a => ¬q a) s).co
untP p
参数：s；p q : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.countP.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p
_1 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Multis
et α),       s =…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `decide_not`：∀ {p : Prop} [g : Decidable p] [h : Decidable ¬p], (decide ¬
p) = !decide p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.countP_eq_countP_filter_add`：∀ {α : Type u_1} (l : List α) (p q : α
 → Bool),   List.countP p l = List.countP p (List.filter q l) + List.countP p (L
ist.filter (fun a => !…
-/
theorem countP_eq_countP_filter_add (s) (p q : α → Prop) [DecidablePred p] [DecidablePred q] :
    countP p s = (filter q s).countP p + (filter (fun a => ¬q a) s).countP p :=
  Quot.inductionOn s fun l => by
    convert! l.countP_eq_countP_filter_add (p ·) (q ·)
    simp
/-
**Multiset.countP_map** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：countP_map (f : α -> β) (s : Multiset α) (p : β -> Prop) [DecidablePred p]
 : countP p (map f s) = card (s.filter fun a => p (f a))
参数：f : α -> β；s : Multiset α；p : β -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_zero`：map_zero (f : α -> β) : map f 0 = 0
· 使用定理 `Multiset.countP_zero`：countP_zero : countP p 0 = 0
· 使用定理 `Multiset.filter_zero`：filter_zero : filter p 0 = 0
· 使用定理 `Multiset.card_zero`：card_zero : @card α 0 = 0
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.countP_cons`：countP_cons (b : α) (s) : countP p (b ::ₘ s) = cou
ntP p s + if p b then 1 else 0
· 使用定理 `Multiset.filter_cons`：filter_cons {a : α} (s : Multiset α) : filter p (a
 ::ₘ s) = (if p a then {a} else 0) + filter p s
· 使用定理 `Multiset.card_add`：card_add (s t : Multiset α) : card (s + t) = card s +
 card t
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `Multiset.card_singleton`：card_singleton (a : α) : card ({a} : Multiset α
) = 1
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
-/
theorem countP_map (f : α → β) (s : Multiset α) (p : β → Prop) [DecidablePred p] :
    countP p (map f s) = card (s.filter fun a => p (f a)) := by
  refine Multiset.induction_on s ?_ fun a t IH => ?_
  · rw [map_zero, countP_zero, filter_zero, card_zero]
  · rw [map_cons, countP_cons, IH, filter_cons, card_add, apply_ite card, card_zero, card_singleton,
      Nat.add_comm]
/-
**Multiset.filter_attach** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：filter_attach (s : Multiset α) (p : α -> Prop) [DecidablePred p] : (s.atta
ch.filter fun a : {a // a in s} => p ↑a) = (s.filter p).attach.map (Subtype.map 
id fun _ => Multiset.mem_of_mem_filter)
参数：s : Multiset α；p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `Multiset.mem_of_mem_filter`：mem_of_mem_filter {a : α} {s} (h : a in filt
er p s) : a in s
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.mem_of_mem_filter`：mem_of_mem_filter {a : α} {l} (h : a in filter p
 l) : a in l
· 使用引理 `List.filter_attach`：filter_attach (l : List α) (p : α -> Bool) : (l.atta
ch.filter fun x => p x : List {x // x in l}) = (l.filter p).attach.map (Subtype.
map id f…
-/
lemma filter_attach (s : Multiset α) (p : α → Prop) [DecidablePred p] :
    (s.attach.filter fun a : {a // a ∈ s} ↦ p ↑a) =
      (s.filter p).attach.map (Subtype.map id fun _ ↦ Multiset.mem_of_mem_filter) :=
  Quotient.inductionOn s fun l ↦ congr_arg _ (List.filter_attach l p)

end

/-! ### Multiplicity of an element -/


section

variable [DecidableEq α] {s t u : Multiset α}

@[simp]
/-
**Multiset.count_filter_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_filter_of_pos {p} [DecidablePred p] {a} {s : Multiset α} (h : p a) :
 count a (filter p s) = count a s
参数：h : p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.coe_count`：coe_count (a : α) (l : List α) : count a (ofList l) 
= l.count a
· 使用定理 `List.count_filter`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {p : α 
→ Bool} {a : α} {l : List α},   p a = true → List.count a (List.filter p l) = Li
st.coun…
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
-/
theorem count_filter_of_pos {p} [DecidablePred p] {a} {s : Multiset α} (h : p a) :
    count a (filter p s) = count a s :=
  Quot.inductionOn s fun _l => by
    simp only [quot_mk_to_coe'', filter_coe, coe_count]
    apply count_filter
    simpa using h
/-
**Multiset.count_filter_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_filter_of_neg {p} [DecidablePred p] {a} {s : Multiset α} (h : ¬p a) 
: count a (filter p s) = 0
参数：h : ¬p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count_eq_zero_of_notMem`：count_eq_zero_of_notMem {a : α} {s : M
ultiset α} (h : a ∉ s) : count a s = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem count_filter_of_neg {p} [DecidablePred p] {a} {s : Multiset α} (h : ¬p a) :
    count a (filter p s) = 0 := by
  simp [h]
/-
**Multiset.count_filter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_filter {p} [DecidablePred p] {a} {s : Multiset α} : count a (filter 
p s) = if p a then count a s else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Multiset.count_filter_of_pos`：count_filter_of_pos {p} [DecidablePred p] 
{a} {s : Multiset α} (h : p a) : count a (filter p s) = count a s
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Multiset.count_filter_of_neg`：count_filter_of_neg {p} [DecidablePred p] 
{a} {s : Multiset α} (h : ¬p a) : count a (filter p s) = 0
-/
theorem count_filter {p} [DecidablePred p] {a} {s : Multiset α} :
    count a (filter p s) = if p a then count a s else 0 := by
  split_ifs with h
  · exact count_filter_of_pos h
  · exact count_filter_of_neg h
/-
**Multiset.count_map** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_map {α β : Type*} (f : α -> β) (s : Multiset α) [DecidableEq β] (b :
 β) : count b (map f s) = card (s.filter fun a => b = f a)
参数：f : α -> β；s : Multiset α；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.countP_map`：countP_map (f : α -> β) (s : Multiset α) (p : β -> 
Prop) [DecidablePred p] : countP p (map f s) = card (s.filter fun a => p (f a))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem count_map {α β : Type*} (f : α → β) (s : Multiset α) [DecidableEq β] (b : β) :
    count b (map f s) = card (s.filter fun a => b = f a) := by
  simp [count, countP_map]

/-- `Multiset.map f` preserves `count` if `f` is injective on the set of elements contained in
the multiset -/
/-
**Multiset.count_map_eq_count** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_map_eq_count [DecidableEq β] (f : α -> β) (s : Multiset α) (hf : Set
.InjOn f { x : α | x in s }) (x) (H : x in s) : (s.map f).count (f x) = s.count 
x
参数：f : α -> β；s : Multiset α；hf : Set.InjOn f { x : α | x in s }；x；H : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.eq_replicate_card`：eq_replicate_card {a : α} {s : Multiset α} :
 s = replicate (card s) a ↔ forall b in s, b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_filter`：mem_filter {a : α} {s} : a in filter p s ↔ a in s ∧
 p a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.filter_congr`：filter_congr {p q : α -> Prop} [DecidablePred p] 
[DecidablePred q] {s : Multiset α} : (forall x in s, p x ↔ q x) -> filter p s = 
filter q s
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.count_replicate_self`：count_replicate_self (a : α) (n : Nat) : 
count a (replicate n a) = n
· 使用定理 `Multiset.card_replicate`：∀ {α : Type u_1} (n : ℕ) (a : α), (Multiset.rep
licate n a).card = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.count.eq_1`：∀ {α : Type u_1} [inst : DecidableEq α] (a : α), Mu
ltiset.count a = Multiset.countP fun x => a = x
· 使用定理 `Multiset.countP_map`：countP_map (f : α -> β) (s : Multiset α) (p : β -> 
Prop) [DecidablePred p] : countP p (map f s) = card (s.filter fun a => p (f a))
· 使用定理 `Multiset.count_filter_of_pos`：count_filter_of_pos {p} [DecidablePred p] 
{a} {s : Multiset α} (h : p a) : count a (filter p s) = count a s

--- 原说明 ---
`Multiset.map f` preserves `count` if `f` is injective on the set of elements co
ntained in
the multiset
-/
theorem count_map_eq_count [DecidableEq β] (f : α → β) (s : Multiset α)
    (hf : Set.InjOn f { x : α | x ∈ s }) (x) (H : x ∈ s) : (s.map f).count (f x) = s.count x := by
  suffices (filter (fun a : α => f x = f a) s).count x = card (filter (fun a : α => f x = f a) s) by
    rw [count, countP_map, ← this]
    exact count_filter_of_pos <| rfl
  · rw [eq_replicate_card.2 fun b hb => (hf H (mem_filter.1 hb).left _).symm]
    · simp
    · simp only [mem_filter, and_imp, @eq_comm _ (f x), imp_self, implies_true]

/-- `Multiset.map f` preserves `count` if `f` is injective -/
/-
**Multiset.count_map_eq_count'** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_map_eq_count' [DecidableEq β] (f : α -> β) (s : Multiset α) (hf : Fu
nction.Injective f) (x : α) : (s.map f).count (f x) = s.count x
参数：f : α -> β；s : Multiset α；hf : Function.Injective f；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.count_map_eq_count`：count_map_eq_count [DecidableEq β] (f : α -
> β) (s : Multiset α) (hf : Set.InjOn f { x : α | x in s }) (x) (H : x in s) : (
s.map f).count (f…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count_eq_zero_of_notMem`：count_eq_zero_of_notMem {a : α} {s : M
ultiset α} (h : a ∉ s) : count a s = 0
· 使用定理 `Multiset.count_eq_zero`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Mul
tiset α} {a : α}, Multiset.count a s = 0 ↔ a ∉ s
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b

--- 原说明 ---
`Multiset.map f` preserves `count` if `f` is injective
-/
theorem count_map_eq_count' [DecidableEq β] (f : α → β) (s : Multiset α) (hf : Function.Injective f)
    (x : α) : (s.map f).count (f x) = s.count x := by
  by_cases H : x ∈ s
  · exact count_map_eq_count f _ hf.injOn _ H
  · rw [count_eq_zero_of_notMem H, count_eq_zero, mem_map]
    rintro ⟨k, hks, hkx⟩
    rw [hf hkx] at hks
    contradiction
/-
**Multiset.filter_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filter_eq' (s : Multiset α) (b : α) : s.filter (· = b) = replicate (count 
b s) b
参数：s : Multiset α；b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.coe_count`：coe_count (a : α) (l : List α) : count a (ofList l) 
= l.count a
· 使用定理 `List.filter_eq`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] [inst_2 : 
DecidableEq α] {l : List α} (a : α),   List.filter (fun x => decide (x = a)) l =
 Lis…
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `Multiset.coe_replicate`：coe_replicate (n : Nat) (a : α) : (List.replicat
e n a : Multiset α) = replicate n a
-/
theorem filter_eq' (s : Multiset α) (b : α) : s.filter (· = b) = replicate (count b s) b :=
  Quotient.inductionOn s fun l => by
    simp only [quot_mk_to_coe, filter_coe, coe_count]
    rw [List.filter_eq, coe_replicate]
/-
**Multiset.filter_eq** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filter_eq (s : Multiset α) (b : α) : s.filter (Eq b) = replicate (count b 
s) b
参数：s : Multiset α；b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.filter_congr`：filter_congr {p q : α -> Prop} [DecidablePred p] 
[DecidablePred q] {s : Multiset α} : (forall x in s, p x ↔ q x) -> filter p s = 
filter q s
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem filter_eq (s : Multiset α) (b : α) : s.filter (Eq b) = replicate (count b s) b := by
  simp_rw [← filter_eq', eq_comm]

end

/-! ### Subtraction -/

section sub
variable [DecidableEq α] {s t u : Multiset α} {a : α}

@[simp]
/-
**Multiset.filter_sub** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：filter_sub (p : α -> Prop) [DecidablePred p] (s t : Multiset α) : filter p
 (s - t) = filter p s - filter p t
参数：p : α -> Prop；s t : Multiset α。
该定理/引理给出了一组等式。
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
· 使用定理 `Multiset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p
_1 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Multis
et α),       s =…
· 使用定理 `Multiset.sub_zero`：∀ {α : Type u_1} [inst : DecidableEq α] (s : Multiset
 α), s - 0 = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `Multiset.sub_cons`：sub_cons (a : α) (s t : Multiset α) : s - a ::ₘ t = s
.erase a - t
· 使用定理 `Multiset.filter_cons_of_pos`：filter_cons_of_pos {a : α} (s) : p a -> fil
ter p (a ::ₘ s) = a ::ₘ filter p s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.cons_inj_right`：cons_inj_right (a : α) : forall {s t : Multiset
 α}, a ::ₘ s = a ::ₘ t ↔ s = t
· 使用定理 `Multiset.cons_erase`：cons_erase {s : Multiset α} {a : α} : a in s -> a :
:ₘ s.erase a = s
· 使用定理 `Multiset.mem_filter_of_mem`：mem_filter_of_mem {a : α} {l} (m : a in l) (
h : p a) : a in filter p l
· 使用定理 `Multiset.erase_of_notMem`：erase_of_notMem {a : α} {s : Multiset α} : a ∉
 s -> s.erase a = s
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Multiset.mem_of_mem_filter`：mem_of_mem_filter {a : α} {s} (h : a in filt
er p s) : a in s
· 使用定理 `Multiset.filter_cons_of_neg`：filter_cons_of_neg {a : α} (s) : ¬p a -> fi
lter p (a ::ₘ s) = filter p s
-/
lemma filter_sub (p : α → Prop) [DecidablePred p] (s t : Multiset α) :
    filter p (s - t) = filter p s - filter p t := by
  revert s; refine Multiset.induction_on t (by simp) fun a t IH s => ?_
  rw [sub_cons, IH]
  by_cases h : p a
  · rw [filter_cons_of_pos _ h, sub_cons]
    congr
    by_cases m : a ∈ s
    · rw [← cons_inj_right a, ← filter_cons_of_pos _ h, cons_erase (mem_filter_of_mem m h),
        cons_erase m]
    · rw [erase_of_notMem m, erase_of_notMem (mt mem_of_mem_filter m)]
  · rw [filter_cons_of_neg _ h]
    by_cases m : a ∈ s
    · rw [(by rw [filter_cons_of_neg _ h] : filter p (erase s a) = filter p (a ::ₘ erase s a)),
        cons_erase m]
    · rw [erase_of_notMem m]

@[simp]
/-
**Multiset.sub_filter_eq_filter_not** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：sub_filter_eq_filter_not (p : α -> Prop) [DecidablePred p] (s : Multiset α
) : s - s.filter p = s.filter fun a => ¬ p a
参数：p : α -> Prop；s : Multiset α。
该定理/引理给出了一组等式。
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
· 使用定理 `Multiset.count_filter_of_pos`：count_filter_of_pos {p} [DecidablePred p] 
{a} {s : Multiset α} (h : p a) : count a (filter p s) = count a s
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用定理 `Multiset.count_eq_zero_of_notMem`：count_eq_zero_of_notMem {a : α} {s : M
ultiset α} (h : a ∉ s) : count a s = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
lemma sub_filter_eq_filter_not (p : α → Prop) [DecidablePred p] (s : Multiset α) :
    s - s.filter p = s.filter fun a ↦ ¬ p a := by ext a; by_cases h : p a <;> simp [h]

end sub

section Embedding

@[simp]
/-
**Multiset.map_le_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_le_map_iff {f : α -> β} (hf : Function.Injective f) {s t : Multiset α}
 : s.map f <= t.map f ↔ s <= t
参数：hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.le_iff_count`：le_iff_count {s t : Multiset α} : s <= t ↔ forall
 a, count a s <= count a t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count_map_eq_count'`：count_map_eq_count' [DecidableEq β] (f : α
 -> β) (s : Multiset α) (hf : Function.Injective f) (x : α) : (s.map f).count (f
 x) = s.count x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.map_le_map`：map_le_map {f : α -> β} {s t : Multiset α} (h : s <
= t) : map f s <= map f t
-/
theorem map_le_map_iff {f : α → β} (hf : Function.Injective f) {s t : Multiset α} :
    s.map f ≤ t.map f ↔ s ≤ t := by
  classical
    refine ⟨fun h => le_iff_count.mpr fun a => ?_, map_le_map⟩
    simpa [count_map_eq_count' f _ hf] using le_iff_count.mp h (f a)

/-- Associate to an embedding `f` from `α` to `β` the order embedding that maps a multiset to its
image under `f`. -/
@[simps!]
/-
**Multiset.mapEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：mapEmbedding (f : α ↪ β) : Multiset α ↪o Multiset β
参数：f : α ↪ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Associate to an embedding `f` from `α` to `β` the order embedding that maps a mu
ltiset to its
image under `f`.
-/
def mapEmbedding (f : α ↪ β) : Multiset α ↪o Multiset β :=
  OrderEmbedding.ofMapLEIff (map f) fun _ _ => map_le_map_iff f.inj'

end Embedding

/-
**Multiset.count_eq_card_filter_eq** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_eq_card_filter_eq [DecidableEq α] (s : Multiset α) (a : α) : s.count
 a = card (s.filter (a = ·))
参数：s : Multiset α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count.eq_1`：∀ {α : Type u_1} [inst : DecidableEq α] (a : α), Mu
ltiset.count a = Multiset.countP fun x => a = x
· 使用定理 `Multiset.countP_eq_card_filter`：countP_eq_card_filter (s) : countP p s =
 card (filter p s)
-/
theorem count_eq_card_filter_eq [DecidableEq α] (s : Multiset α) (a : α) :
    s.count a = card (s.filter (a = ·)) := by rw [count, countP_eq_card_filter]

/--
Mapping a multiset through a predicate and counting the `True`s yields the cardinality of the set
filtered by the predicate. Note that this uses the notion of a multiset of `Prop`s - due to the
decidability requirements of `count`, the decidability instance on the LHS is different from the
RHS. In particular, the decidability instance on the left leaks `Classical.decEq`.
See [here](https://github.com/leanprover-community/mathlib/pull/11306#discussion_r782286812)
for more discussion.
-/
@[simp]
/-
**Multiset.map_count_True_eq_filter_card** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_count_True_eq_filter_card (s : Multiset α) (p : α -> Prop) [DecidableP
red p] : (s.map p).count True = card (s.filter p)
参数：s : Multiset α；p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count_eq_card_filter_eq`：count_eq_card_filter_eq [DecidableEq α
] (s : Multiset α) (a : α) : s.count a = card (s.filter (a = ·))
· 使用定理 `Multiset.filter_map`：filter_map (f : β -> α) (s : Multiset β) : filter p
 (map f s) = map f (filter (p ∘ f) s)
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.filter_congr`：filter_congr {p q : α -> Prop} [DecidablePred p] 
[DecidablePred q] {s : Multiset α} : (forall x in s, p x ↔ q x) -> filter p s = 
filter q s
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Mapping a multiset through a predicate and counting the `True`s yields the cardi
nality of the set
filtered by the predicate. Note that this uses the notion of a multiset of `Prop
`s - due to the
decidability requirements of `count`, the decidability instance on the LHS is di
fferent from the
RHS. In particular, the decidability instance on the left leaks `Classical.decEq
`.
See [here](https://github.com/leanprover-community/mathlib/pull/11306#discussion
_r782286812)
for more discussion.
-/
theorem map_count_True_eq_filter_card (s : Multiset α) (p : α → Prop) [DecidablePred p] :
    (s.map p).count True = card (s.filter p) := by
  simp only [count_eq_card_filter_eq, eq_iff_iff, true_iff, filter_map, comp_apply, card_map]

section Map

set_option backward.isDefEq.respectTransparency false in
/-
**Multiset.filter_attach'** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：filter_attach' (s : Multiset α) (p : {a // a in s} -> Prop) [DecidableEq α
] [DecidablePred p] : s.attach.filter p = (s.filter fun x => exists h, p ⟨x, h⟩)
.attach.map (Subtype.map id fun _ => mem_of_mem_filter)
参数：s : Multiset α；p : {a // a in s} -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.map_injective`：map_injective {f : α -> β} (hf : Function.Inject
ive f) : Function.Injective (Multiset.map f)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Multiset.mem_of_mem_filter`：mem_of_mem_filter {a : α} {s} (h : a in filt
er p s) : a in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Multiset.map_filter'`：map_filter' {f : α -> β} (hf : Injective f) (s : M
ultiset α) [DecidablePred fun b => exists a, p a ∧ f a = b] : (s.filter p).map f
 = (s.map …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.filter_congr`：filter_congr {p q : α -> Prop} [DecidablePred p] 
[DecidablePred q] {s : Multiset α} : (forall x in s, p x ↔ q x) -> filter p s = 
filter q s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Multiset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p
_1 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Multis
et α),       s =…
· 使用定理 `Multiset.attach_map_val`：attach_map_val (s : Multiset α) : s.attach.map 
Subtype.val = s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma filter_attach' (s : Multiset α) (p : {a // a ∈ s} → Prop) [DecidableEq α]
    [DecidablePred p] :
    s.attach.filter p =
      (s.filter fun x ↦ ∃ h, p ⟨x, h⟩).attach.map (Subtype.map id fun _ ↦ mem_of_mem_filter) := by
  classical
  refine Multiset.map_injective Subtype.val_injective ?_
  rw [map_filter' _ Subtype.val_injective]
  simp only [Subtype.exists, exists_and_right, exists_eq_right, attach_map_val, Subtype.map, id,
    map_map, comp]

end Map

section Nodup

variable {s : Multiset α}

/-
**Multiset.Nodup.filter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred p] {s : Multiset α},
 s.Nodup → (Multiset.filter p s).Nodup
参数：p : α → Prop；Multiset.filter p s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用定理 `List.Nodup.filter`：∀ {α : Type u} (p : α → Bool) {l : List α}, l.Nodup →
 (List.filter p l).Nodup
-/
theorem Nodup.filter (p : α → Prop) [DecidablePred p] {s} : Nodup s → Nodup (filter p s) :=
  Quot.induction_on s fun _ => List.Nodup.filter (p ·)
/-
**Multiset.Nodup.erase_eq_filter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (a : α) {s : Multiset α},   s.Nodu
p → s.erase a = Multiset.filter (fun x => x ≠ a) s
参数：a : α；fun x => x ≠ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `decide_not`：∀ {p : Prop} [g : Decidable p] [h : Decidable ¬p], (decide ¬
p) = !decide p
· 使用定理 `List.Nodup.erase_eq_filter`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α
] {l : List α},   l.Nodup → ∀ (a : α), l.erase a = List.filter (fun x => x != a)
 l
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem Nodup.erase_eq_filter [DecidableEq α] (a : α) {s} :
    Nodup s → s.erase a = Multiset.filter (· ≠ a) s :=
  Quot.induction_on s fun _ d =>
    congr_arg ((↑) : List α → Multiset α) <| by simpa using! List.Nodup.erase_eq_filter d a
/-
**Multiset.Nodup.filterMap** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} {β : Type v} {s : Multiset α} (f : α → Option β),   (∀ (a
 a' : α), ∀ b ∈ f a, b ∈ f a' → a = a') → s.Nodup → (Multiset.filterMap f s).Nod
up
参数：f : α → Option β；∀ (a a' : α), ∀ b ∈ f a, b ∈ f a' → a = a'；Multiset.filterMa
p f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用定理 `List.Nodup.filterMap`：∀ {α : Type u} {β : Type v} {l : List α} {f : α → 
Option β},   (∀ (a a' : α), ∀ b ∈ f a, b ∈ f a' → a = a') → l.Nodup → (List.filt
erMap f l)…
-/
protected theorem Nodup.filterMap (f : α → Option β) (H : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a') :
    Nodup s → Nodup (filterMap f s) :=
  Quot.induction_on s fun _ => List.Nodup.filterMap H
/-
**Multiset.Nodup.mem_erase_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {a b : α} {l : Multiset α}, l.Nodu
p → (a ∈ l.erase b ↔ a ≠ b ∧ a ∈ l)
参数：a ∈ l.erase b ↔ a ≠ b ∧ a ∈ l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Nodup.erase_eq_filter`：∀ {α : Type u_1} [inst : DecidableEq α] 
(a : α) {s : Multiset α},   s.Nodup → s.erase a = Multiset.filter (fun x => x ≠ 
a) s
· 使用定理 `Multiset.mem_filter`：mem_filter {a : α} {s} : a in filter p s ↔ a in s ∧
 p a
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Nodup.mem_erase_iff [DecidableEq α] {a b : α} {l} (d : Nodup l) :
    a ∈ l.erase b ↔ a ≠ b ∧ a ∈ l := by
  rw [d.erase_eq_filter b, mem_filter, and_comm]
/-
**Multiset.Nodup.notMem_erase** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {a : α} {s : Multiset α}, s.Nodup 
→ a ∉ s.erase a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.Nodup.mem_erase_iff`：∀ {α : Type u_1} [inst : DecidableEq α] {a
 b : α} {l : Multiset α}, l.Nodup → (a ∈ l.erase b ↔ a ≠ b ∧ a ∈ l)
-/
theorem Nodup.notMem_erase [DecidableEq α] {a : α} {s} (h : Nodup s) : a ∉ s.erase a := fun ha =>
  (h.mem_erase_iff.1 ha).1 rfl

end Nodup

end Multiset

