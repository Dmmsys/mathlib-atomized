/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Peter Nelson
-/
module

public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.WellFounded

/-!
# Minimality and Maximality

This file proves basic facts about minimality and maximality
of an element with respect to a predicate `P` on an ordered type `α`.

## Implementation Details

This file underwent a refactor from a version where minimality and maximality were defined using
sets rather than predicates, and with an unbundled order relation rather than a `LE` instance.

A side effect is that it has become less straightforward to state that something is minimal
with respect to a relation that is *not* defeq to the default `LE`.
One possible way would be with a type synonym,
and another would be with an ad hoc `LE` instance and `@` notation.
This was not an issue in practice anywhere in mathlib at the time of the refactor,
but it may be worth re-examining this to make it easier in the future; see the TODO below.

## TODO

* In the linearly ordered case, versions of lemmas like `minimal_mem_image` will hold with
  `MonotoneOn`/`AntitoneOn` assumptions rather than the stronger `x ≤ y ↔ f x ≤ f y` assumptions.

* `Set.maximal_iff_forall_insert` and `Set.minimal_iff_forall_sdiff_singleton` will generalize to
  lemmas about covering in the case of an `IsStronglyAtomic`/`IsStronglyCoatomic` order.

* `Finset` versions of the lemmas about sets.

* API to allow for easily expressing min/maximality with respect to an arbitrary non-`LE` relation.
* API for `MinimalFor`/`MaximalFor`
-/

@[expose] public section

assert_not_exists CompleteLattice

open Set OrderDual

variable {ι α β : Type*}

section LE
variable [LE α] {P Q : ι → Prop} {f : ι → α} {i j : ι}

@[to_dual (attr := simp)]
/-
**minimalFor_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：minimalFor_eq_iff : MinimalFor (· = j) f i ↔ i = j
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
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma minimalFor_eq_iff : MinimalFor (· = j) f i ↔ i = j := by simp +contextual [MinimalFor]

@[to_dual (attr := gcongr)]
/-
**MinimalFor.anti** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MinimalFor.anti (h : MinimalFor P f i) (hle : Q <= P) (hQ : Q i) : Minimal
For Q f i
参数：h : MinimalFor P f i；hle : Q <= P；hQ : Q i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MinimalFor.le_of_le`：MinimalFor.le_of_le (h : MinimalFor P f i) (hj : P 
j) (hji : f j <= f i) : f i <= f j
-/
theorem MinimalFor.anti (h : MinimalFor P f i) (hle : Q ≤ P) (hQ : Q i) : MinimalFor Q f i :=
  ⟨hQ, (h.le_of_le <| hle · ·)⟩

end LE

variable {P Q : α → Prop} {a x y : α}

section LE
variable [LE α]

@[to_dual (attr := simp)]
/-
**minimalFor_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：minimalFor_id : MinimalFor P id x ↔ Minimal P x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma minimalFor_id : MinimalFor P id x ↔ Minimal P x := .rfl

@[to_dual (attr := simp)]
/-
**minimal_toDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minimal_toDual : Minimal (fun x => P (ofDual x)) (toDual x) ↔ Maximal P x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem minimal_toDual : Minimal (fun x ↦ P (ofDual x)) (toDual x) ↔ Maximal P x :=
  Iff.rfl

@[to_dual]
alias ⟨Minimal.of_dual, Minimal.dual⟩ := minimal_toDual

@[to_dual (attr := simp)]
/-
**minimal_false** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minimal_false : ¬ Minimal (fun _ => False) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem minimal_false : ¬ Minimal (fun _ ↦ False) x := by
  simp [Minimal]
/-
**minimal_true** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} {x : α} [inst : LE α], Minimal (fun x => True) x ↔ IsMin 
x
参数：fun x => True。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[to_dual (attr := simp)] theorem minimal_true : Minimal (fun _ ↦ True) x ↔ IsMin x := by
  simp [IsMin, Minimal]

@[to_dual (attr := simp)]
/-
**minimal_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minimal_subtype {x : Subtype Q} : Minimal (fun x => P x.1) x ↔ Minimal (P 
⊓ Q) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem minimal_subtype {x : Subtype Q} :
    Minimal (fun x ↦ P x.1) x ↔ Minimal (P ⊓ Q) x := by
  obtain ⟨x, hx⟩ := x
  simp only [Minimal, Subtype.forall, Subtype.mk_le_mk, Pi.inf_apply, inf_Prop_eq]
  tauto

@[to_dual]
/-
**minimal_true_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minimal_true_subtype {x : Subtype P} : Minimal (fun _ => True) x ↔ Minimal
 P x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem minimal_true_subtype {x : Subtype P} : Minimal (fun _ ↦ True) x ↔ Minimal P x := by
  obtain ⟨x, hx⟩ := x
  simp [Minimal, hx]

@[to_dual (attr := simp)]
/-
**minimal_minimal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minimal_minimal : Minimal (Minimal P) x ↔ Minimal P x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Minimal.prop`：Minimal.prop (h : Minimal P x) : P x
· 使用引理 `Minimal.le_of_le`：Minimal.le_of_le (h : Minimal P x) (hy : P y) (hle : y
 <= x) : x <= y
-/
theorem minimal_minimal : Minimal (Minimal P) x ↔ Minimal P x :=
  ⟨fun h ↦ h.prop, fun h ↦ ⟨h, fun _ hy hyx ↦ h.le_of_le hy.prop hyx⟩⟩

/-- If `P` is down-closed, then minimal elements satisfying `P` are exactly the globally minimal
elements satisfying `P`. -/
@[to_dual
/-- If `P` is up-closed, then maximal elements satisfying `P` are exactly the globally maximal
elements satisfying `P`. -/]
/-
**minimal_iff_isMin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minimal_iff_isMin (hP : forall ⦃x y⦄, P y -> x <= y -> P x) : Minimal P x 
↔ P x ∧ IsMin x
参数：hP : forall ⦃x y⦄, P y -> x <= y -> P x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Minimal.prop`：Minimal.prop (h : Minimal P x) : P x
· 使用引理 `Minimal.le_of_le`：Minimal.le_of_le (h : Minimal P x) (hy : P y) (hle : y
 <= x) : x <= y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem minimal_iff_isMin (hP : ∀ ⦃x y⦄, P y → x ≤ y → P x) : Minimal P x ↔ P x ∧ IsMin x :=
  ⟨fun h ↦ ⟨h.prop, fun _ h' ↦ h.le_of_le (hP h.prop h') h'⟩, fun h ↦ ⟨h.1, fun _ _  h' ↦ h.2 h'⟩⟩

@[to_dual]
/-
**Minimal.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Minimal.mono (h : Minimal P x) (hle : Q <= P) (hQ : Q x) : Minimal Q x
参数：h : Minimal P x；hle : Q <= P；hQ : Q x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Minimal.le_of_le`：Minimal.le_of_le (h : Minimal P x) (hy : P y) (hle : y
 <= x) : x <= y
-/
theorem Minimal.mono (h : Minimal P x) (hle : Q ≤ P) (hQ : Q x) : Minimal Q x :=
  ⟨hQ, fun y hQy ↦ h.le_of_le (hle y hQy)⟩

@[to_dual]
/-
**Minimal.and_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Minimal.and_right (h : Minimal P x) (hQ : Q x) : Minimal (fun x => P x ∧ Q
 x) x
参数：h : Minimal P x；hQ : Q x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Minimal.mono`：Minimal.mono (h : Minimal P x) (hle : Q <= P) (hQ : Q x) :
 Minimal Q x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Minimal.prop`：Minimal.prop (h : Minimal P x) : P x
-/
theorem Minimal.and_right (h : Minimal P x) (hQ : Q x) : Minimal (fun x ↦ P x ∧ Q x) x :=
  h.mono (fun _ ↦ And.left) ⟨h.prop, hQ⟩

@[to_dual]
/-
**Minimal.and_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Minimal.and_left (h : Minimal P x) (hQ : Q x) : Minimal (fun x => (Q x ∧ P
 x)) x
参数：h : Minimal P x；hQ : Q x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Minimal.mono`：Minimal.mono (h : Minimal P x) (hle : Q <= P) (hQ : Q x) :
 Minimal Q x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Minimal.prop`：Minimal.prop (h : Minimal P x) : P x
-/
theorem Minimal.and_left (h : Minimal P x) (hQ : Q x) : Minimal (fun x ↦ (Q x ∧ P x)) x :=
  h.mono (fun _ ↦ And.right) ⟨hQ, h.prop⟩
/-
**minimal_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} {x y : α} [inst : LE α], Minimal (fun x => x = y) x ↔ x =
 y
参数：fun x => x = y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[to_dual (attr := simp)] theorem minimal_eq_iff : Minimal (· = y) x ↔ x = y := by
  simp +contextual [Minimal]

@[to_dual]
/-
**not_minimal_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_minimal_iff (hx : P x) : ¬ Minimal P x ↔ exists y, P y ∧ y <= x ∧ ¬ (x
 <= y)
参数：hx : P x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_minimal_iff (hx : P x) : ¬ Minimal P x ↔ ∃ y, P y ∧ y ≤ x ∧ ¬ (x ≤ y) := by
  simp [Minimal, hx]

@[to_dual]
/-
**Minimal.or** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Minimal.or (h : Minimal (fun x => P x ∨ Q x) x) : Minimal P x ∨ Minimal Q 
x
参数：h : Minimal (fun x => P x ∨ Q x) x。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Minimal.or (h : Minimal (fun x ↦ P x ∨ Q x) x) : Minimal P x ∨ Minimal Q x := by
  obtain ⟨h | h, hmin⟩ := h
  · exact .inl ⟨h, fun y hy hyx ↦ hmin (Or.inl hy) hyx⟩
  exact .inr ⟨h, fun y hy hyx ↦ hmin (Or.inr hy) hyx⟩

@[to_dual]
/-
**minimal_and_iff_right_of_imp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minimal_and_iff_right_of_imp (hPQ : forall ⦃x⦄, P x -> Q x) : Minimal (fun
 x => P x ∧ Q x) x ↔ (Minimal P x) ∧ Q x
参数：hPQ : forall ⦃x⦄, P x -> Q x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_iff_left_of_imp`：∀ {a b : Prop}, (a → b) → (a ∧ b ↔ a)
· 使用引理 `Minimal.prop`：Minimal.prop (h : Minimal P x) : P x
-/
theorem minimal_and_iff_right_of_imp (hPQ : ∀ ⦃x⦄, P x → Q x) :
    Minimal (fun x ↦ P x ∧ Q x) x ↔ (Minimal P x) ∧ Q x := by
  simp_rw [and_iff_left_of_imp (fun x ↦ hPQ x), iff_self_and]
  exact fun h ↦ hPQ h.prop

@[to_dual]
/-
**minimal_and_iff_left_of_imp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minimal_and_iff_left_of_imp (hPQ : forall ⦃x⦄, P x -> Q x) : Minimal (fun 
x => Q x ∧ P x) x ↔ Q x ∧ (Minimal P x)
参数：hPQ : forall ⦃x⦄, P x -> Q x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `minimal_and_iff_right_of_imp`：minimal_and_iff_right_of_imp (hPQ : forall
 ⦃x⦄, P x -> Q x) : Minimal (fun x => P x ∧ Q x) x ↔ (Minimal P x) ∧ Q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem minimal_and_iff_left_of_imp (hPQ : ∀ ⦃x⦄, P x → Q x) :
    Minimal (fun x ↦ Q x ∧ P x) x ↔ Q x ∧ (Minimal P x) := by
  simp_rw [iff_comm, and_comm, minimal_and_iff_right_of_imp hPQ, and_comm]

end LE

section Preorder

variable [Preorder α] [Preorder β] {Q : ι → Prop} {f : ι → α} {g : α → β} {i j : ι}

@[to_dual maximal_iff_forall_gt]
/-
**minimal_iff_forall_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minimal_iff_forall_lt : Minimal P x ↔ P x ∧ forall ⦃y⦄, y < x -> ¬ P y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem minimal_iff_forall_lt : Minimal P x ↔ P x ∧ ∀ ⦃y⦄, y < x → ¬ P y := by
  simp [Minimal, lt_iff_le_not_ge, imp.swap]

@[to_dual maximalFor_iff_forall_gt]
/-
**minimalFor_iff_forall_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minimalFor_iff_forall_lt : MinimalFor Q f i ↔ Q i ∧ forall ⦃j⦄, f j < f i 
-> ¬ Q j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem minimalFor_iff_forall_lt : MinimalFor Q f i ↔ Q i ∧ ∀ ⦃j⦄, f j < f i → ¬ Q j := by
  simp [MinimalFor, lt_iff_le_not_ge, imp.swap]

@[to_dual not_prop_of_gt]
/-
**Minimal.not_prop_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Minimal.not_prop_of_lt (h : Minimal P x) (hlt : y < x) : ¬ P y
参数：h : Minimal P x；hlt : y < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `minimal_iff_forall_lt`：minimal_iff_forall_lt : Minimal P x ↔ P x ∧ foral
l ⦃y⦄, y < x -> ¬ P y
-/
theorem Minimal.not_prop_of_lt (h : Minimal P x) (hlt : y < x) : ¬ P y :=
  (minimal_iff_forall_lt.1 h).2 hlt

@[to_dual not_prop_of_gt]
/-
**MinimalFor.not_prop_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MinimalFor.not_prop_of_lt (h : MinimalFor Q f i) (hlt : f j < f i) : ¬ Q j
参数：h : MinimalFor Q f i；hlt : f j < f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `minimalFor_iff_forall_lt`：minimalFor_iff_forall_lt : MinimalFor Q f i ↔ 
Q i ∧ forall ⦃j⦄, f j < f i -> ¬ Q j
-/
theorem MinimalFor.not_prop_of_lt (h : MinimalFor Q f i) (hlt : f j < f i) : ¬ Q j :=
  (minimalFor_iff_forall_lt.1 h).2 hlt

@[to_dual not_gt]
/-
**Minimal.not_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Minimal.not_lt (h : Minimal P x) (hy : P y) : ¬(y < x)
参数：h : Minimal P x；hy : P y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Minimal.not_prop_of_lt`：Minimal.not_prop_of_lt (h : Minimal P x) (hlt : 
y < x) : ¬ P y
-/
theorem Minimal.not_lt (h : Minimal P x) (hy : P y) : ¬(y < x) :=
  fun hlt ↦ h.not_prop_of_lt hlt hy

@[to_dual not_gt]
/-
**MinimalFor.not_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MinimalFor.not_lt (h : MinimalFor Q f i) (hj : Q j) : ¬(f j < f i)
参数：h : MinimalFor Q f i；hj : Q j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MinimalFor.not_prop_of_lt`：MinimalFor.not_prop_of_lt (h : MinimalFor Q f
 i) (hlt : f j < f i) : ¬ Q j
-/
theorem MinimalFor.not_lt (h : MinimalFor Q f i) (hj : Q j) : ¬(f j < f i) :=
  fun hlt ↦ h.not_prop_of_lt hlt hj

@[to_dual (attr := simp) maximal_ge_iff]
/-
**minimal_le_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minimal_le_iff : Minimal (· <= y) x ↔ x <= y ∧ IsMin x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minimal_iff_isMin`：minimal_iff_isMin (hP : forall ⦃x y⦄, P y -> x <= y -
> P x) : Minimal P x ↔ P x ∧ IsMin x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem minimal_le_iff : Minimal (· ≤ y) x ↔ x ≤ y ∧ IsMin x :=
  minimal_iff_isMin (fun _ _ h h' ↦ h'.trans h)

@[to_dual (attr := simp) maximal_gt_iff]
/-
**minimal_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minimal_lt_iff : Minimal (· < y) x ↔ x < y ∧ IsMin x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minimal_iff_isMin`：minimal_iff_isMin (hP : forall ⦃x y⦄, P y -> x <= y -
> P x) : Minimal P x ↔ P x ∧ IsMin x
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
-/
theorem minimal_lt_iff : Minimal (· < y) x ↔ x < y ∧ IsMin x :=
  minimal_iff_isMin (fun _ _ h h' ↦ h'.trans_lt h)

@[to_dual not_maximal_iff_exists_gt]
/-
**not_minimal_iff_exists_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_minimal_iff_exists_lt (hx : P x) : ¬ Minimal P x ↔ exists y, y < x ∧ P
 y
参数：hx : P x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_minimal_iff`：not_minimal_iff (hx : P x) : ¬ Minimal P x ↔ exists y, 
P y ∧ y <= x ∧ ¬ (x <= y)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_minimal_iff_exists_lt (hx : P x) : ¬ Minimal P x ↔ ∃ y, y < x ∧ P y := by
  simp_rw [not_minimal_iff hx, lt_iff_le_not_ge, and_comm]

@[to_dual exists_gt_of_not_maximal]
alias ⟨exists_lt_of_not_minimal, _⟩ := not_minimal_iff_exists_lt

@[to_dual]
/-
**MinimalFor.of_strictMonoOn_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MinimalFor.of_strictMonoOn_comp (hg : StrictMonoOn g (f '' Set.ofPred Q)) 
(h : MinimalFor Q (g ∘ f) i) : MinimalFor Q f i
参数：hg : StrictMonoOn g (f '' Set.ofPred Q)；h : MinimalFor Q (g ∘ f) i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MinimalFor.prop`：MinimalFor.prop (h : MinimalFor P f i) : P i
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `MinimalFor.not_lt`：MinimalFor.not_lt (h : MinimalFor Q f i) (hj : Q j) :
 ¬(f j < f i)
· 使用引理 `lt_of_le_not_ge`：lt_of_le_not_ge (hab : a <= b) (hba : ¬ b <= a) : a < b
-/
theorem MinimalFor.of_strictMonoOn_comp (hg : StrictMonoOn g (f '' Set.ofPred Q))
    (h : MinimalFor Q (g ∘ f) i) : MinimalFor Q f i := by
  refine ⟨h.prop, fun j hj hle ↦ ?_⟩
  by_contra
  exact h.not_lt hj <| hg ⟨j, hj, rfl⟩ ⟨i, h.prop, rfl⟩ <| lt_of_le_not_ge hle this

@[to_dual]
/-
**MinimalFor.minimal_of_strictMonoOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MinimalFor.minimal_of_strictMonoOn (hg : StrictMonoOn g (Set.ofPred P)) (h
 : MinimalFor P g x) : Minimal P x
参数：hg : StrictMonoOn g (Set.ofPred P)；h : MinimalFor P g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `minimalFor_id`：minimalFor_id : MinimalFor P id x ↔ Minimal P x
· 使用定理 `MinimalFor.of_strictMonoOn_comp`：MinimalFor.of_strictMonoOn_comp (hg : S
trictMonoOn g (f '' Set.ofPred Q)) (h : MinimalFor Q (g ∘ f) i) : MinimalFor Q f
 i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
theorem MinimalFor.minimal_of_strictMonoOn (hg : StrictMonoOn g (Set.ofPred P))
    (h : MinimalFor P g x) :
    Minimal P x :=
  minimalFor_id.mp <| .of_strictMonoOn_comp (Set.image_id _ ▸ hg) h

@[to_dual]
/-
**MinimalFor.maximalFor_of_strictAntiOn_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MinimalFor.maximalFor_of_strictAntiOn_comp (hg : StrictAntiOn g (f '' Set.
ofPred Q)) (h : MinimalFor Q (g ∘ f) i) : MaximalFor Q f i
参数：hg : StrictAntiOn g (f '' Set.ofPred Q)；h : MinimalFor Q (g ∘ f) i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MinimalFor.prop`：MinimalFor.prop (h : MinimalFor P f i) : P i
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `MinimalFor.not_lt`：MinimalFor.not_lt (h : MinimalFor Q f i) (hj : Q j) :
 ¬(f j < f i)
· 使用引理 `lt_of_le_not_ge`：lt_of_le_not_ge (hab : a <= b) (hba : ¬ b <= a) : a < b
-/
theorem MinimalFor.maximalFor_of_strictAntiOn_comp (hg : StrictAntiOn g (f '' Set.ofPred Q))
    (h : MinimalFor Q (g ∘ f) i) : MaximalFor Q f i := by
  refine ⟨h.prop, fun j hj hle ↦ ?_⟩
  by_contra
  exact h.not_lt hj <| hg ⟨i, h.prop, rfl⟩ ⟨j, hj, rfl⟩ <| lt_of_le_not_ge hle this

@[to_dual]
/-
**MinimalFor.maximal_of_strictAntiOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MinimalFor.maximal_of_strictAntiOn (hg : StrictAntiOn g (Set.ofPred P)) (h
 : MinimalFor P g x) : Maximal P x
参数：hg : StrictAntiOn g (Set.ofPred P)；h : MinimalFor P g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `maximalFor_id`：∀ {α : Type u_2} {P : α → Prop} {x : α} [inst : LE α], Ma
ximalFor P id x ↔ Maximal P x
· 使用定理 `MinimalFor.maximalFor_of_strictAntiOn_comp`：MinimalFor.maximalFor_of_str
ictAntiOn_comp (hg : StrictAntiOn g (f '' Set.ofPred Q)) (h : MinimalFor Q (g ∘ 
f) i) : MaximalFor Q f i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
theorem MinimalFor.maximal_of_strictAntiOn (hg : StrictAntiOn g (Set.ofPred P))
    (h : MinimalFor P g x) :
    Maximal P x :=
  maximalFor_id.mp <| MinimalFor.maximalFor_of_strictAntiOn_comp (Set.image_id _ ▸ hg) h

section WellFoundedLT
variable [WellFoundedLT α]

@[to_dual]
/-
**exists_minimalFor_of_wellFoundedLT** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_minimalFor_of_wellFoundedLT (P : ι -> Prop) (f : ι -> α) (hP : exis
ts i, P i) : exists i, MinimalFor P f i
参数：P : ι -> Prop；f : ι -> α；hP : exists i, P i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `WellFounded.has_min`：∀ {α : Type u_4} {r : α → α → Prop}, WellFounded r 
→ ∀ (s : Set α), s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
· 使用定理 `instIsWellFoundedInvImage`：∀ {α : Type u} {β : Type v} (r : α → α → Prop
) [IsWellFounded α r] (f : β → α), IsWellFounded β (InvImage r f)
-/
lemma exists_minimalFor_of_wellFoundedLT (P : ι → Prop) (f : ι → α) (hP : ∃ i, P i) :
    ∃ i, MinimalFor P f i := by
  simpa [not_lt_iff_le_imp_ge, InvImage]
    using! (instIsWellFoundedInvImage (· < ·) f).wf.has_min _ hP

@[to_dual]
/-
**exists_minimal_of_wellFoundedLT** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_minimal_of_wellFoundedLT (P : α -> Prop) (hP : exists a, P a) : exi
sts a, Minimal P a
参数：P : α -> Prop；hP : exists a, P a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `exists_minimalFor_of_wellFoundedLT`：exists_minimalFor_of_wellFoundedLT (
P : ι -> Prop) (f : ι -> α) (hP : exists i, P i) : exists i, MinimalFor P f i
-/
lemma exists_minimal_of_wellFoundedLT (P : α → Prop) (hP : ∃ a, P a) : ∃ a, Minimal P a :=
  exists_minimalFor_of_wellFoundedLT P id hP

@[to_dual exists_maximal_ge_of_wellFoundedGT]
/-
**exists_minimal_le_of_wellFoundedLT** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_minimal_le_of_wellFoundedLT (P : α -> Prop) (a : α) (ha : P a) : ex
ists b <= a, Minimal P b
参数：P : α -> Prop；a : α；ha : P a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `exists_minimal_of_wellFoundedLT`：exists_minimal_of_wellFoundedLT (P : α 
-> Prop) (hP : exists a, P a) : exists a, Minimal P a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma exists_minimal_le_of_wellFoundedLT (P : α → Prop) (a : α) (ha : P a) :
    ∃ b ≤ a, Minimal P b := by
  obtain ⟨b, ⟨hba, hb⟩, hbmin⟩ :=
    exists_minimal_of_wellFoundedLT (fun b ↦ b ≤ a ∧ P b) ⟨a, le_rfl, ha⟩
  exact ⟨b, hba, hb, fun c hc hcb ↦ hbmin ⟨hcb.trans hba, hc⟩ hcb⟩

end WellFoundedLT
end Preorder

section PartialOrder

variable [PartialOrder α]

@[to_dual (rename := hge → hle) eq_of_le]
/-
**Minimal.eq_of_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Minimal.eq_of_ge (hx : Minimal P x) (hy : P y) (hge : y <= x) : x = y
参数：hx : Minimal P x；hy : P y；hge : y <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Minimal.eq_of_ge (hx : Minimal P x) (hy : P y) (hge : y ≤ x) : x = y :=
  (hx.2 hy hge).antisymm hge

@[to_dual (rename := hle → hge) eq_of_ge]
/-
**Minimal.eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Minimal.eq_of_le (hx : Minimal P x) (hy : P y) (hle : y <= x) : y = x
参数：hx : Minimal P x；hy : P y；hle : y <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Minimal.eq_of_ge`：Minimal.eq_of_ge (hx : Minimal P x) (hy : P y) (hge : 
y <= x) : x = y
-/
theorem Minimal.eq_of_le (hx : Minimal P x) (hy : P y) (hle : y ≤ x) : y = x :=
  (hx.eq_of_ge hy hle).symm

@[to_dual]
/-
**minimal_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minimal_iff : Minimal P x ↔ P x ∧ forall ⦃y⦄, P y -> y <= x -> x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Minimal.eq_of_ge`：Minimal.eq_of_ge (hx : Minimal P x) (hy : P y) (hge : 
y <= x) : x = y
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem minimal_iff : Minimal P x ↔ P x ∧ ∀ ⦃y⦄, P y → y ≤ x → x = y :=
  ⟨fun h ↦ ⟨h.1, fun _ ↦ h.eq_of_ge⟩, fun h ↦ ⟨h.1, fun _ hy hle ↦ (h.2 hy hle).le⟩⟩

@[to_dual]
/-
**minimal_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minimal_mem_iff {s : Set α} : Minimal (· in s) x ↔ x in s ∧ forall ⦃y⦄, y 
in s -> y <= x -> x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minimal_iff`：minimal_iff : Minimal P x ↔ P x ∧ forall ⦃y⦄, P y -> y <= x
 -> x = y
-/
theorem minimal_mem_iff {s : Set α} : Minimal (· ∈ s) x ↔ x ∈ s ∧ ∀ ⦃y⦄, y ∈ s → y ≤ x → x = y :=
  minimal_iff

/-- If `P y` holds, and everything satisfying `P` is above `y`, then `y` is the unique minimal
element satisfying `P`. -/
@[to_dual
/-- If `P y` holds, and everything satisfying `P` is below `y`, then `y` is the unique maximal
element satisfying `P`. -/]
/-
**minimal_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minimal_iff_eq (hy : P y) (hP : forall ⦃x⦄, P x -> y <= x) : Minimal P x ↔
 x = y
参数：hy : P y；hP : forall ⦃x⦄, P x -> y <= x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Minimal.eq_of_ge`：Minimal.eq_of_ge (hx : Minimal P x) (hy : P y) (hge : 
y <= x) : x = y
· 使用引理 `Minimal.prop`：Minimal.prop (h : Minimal P x) : P x
-/
theorem minimal_iff_eq (hy : P y) (hP : ∀ ⦃x⦄, P x → y ≤ x) : Minimal P x ↔ x = y :=
  ⟨fun h ↦ h.eq_of_ge hy (hP h.prop), by rintro rfl; exact ⟨hy, fun z hz _ ↦ hP hz⟩⟩
/-
**minimal_ge_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} {x y : α} [inst : PartialOrder α], Minimal (fun x => y ≤ 
x) x ↔ x = y
参数：fun x => y ≤ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minimal_iff_eq`：minimal_iff_eq (hy : P y) (hP : forall ⦃x⦄, P x -> y <= 
x) : Minimal P x ↔ x = y
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
@[to_dual (attr := simp) maximal_le_iff] theorem minimal_ge_iff : Minimal (y ≤ ·) x ↔ x = y :=
  minimal_iff_eq rfl.le fun _ ↦ id

@[to_dual]
/-
**minimal_iff_minimal_of_imp_of_forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minimal_iff_minimal_of_imp_of_forall (hPQ : forall ⦃x⦄, Q x -> P x) (h : f
orall ⦃x⦄, P x -> exists y, y <= x ∧ Q y) : Minimal P x ↔ Minimal Q x
参数：hPQ : forall ⦃x⦄, Q x -> P x；h : forall ⦃x⦄, P x -> exists y, y <= x ∧ Q y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Minimal.prop`：Minimal.prop (h : Minimal P x) : P x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `Minimal.le_of_le`：Minimal.le_of_le (h : Minimal P x) (hy : P y) (hle : y
 <= x) : x <= y
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem minimal_iff_minimal_of_imp_of_forall (hPQ : ∀ ⦃x⦄, Q x → P x)
    (h : ∀ ⦃x⦄, P x → ∃ y, y ≤ x ∧ Q y) : Minimal P x ↔ Minimal Q x := by
  refine ⟨fun h' ↦ ⟨?_, fun y hy hyx ↦ h'.le_of_le (hPQ hy) hyx⟩,
    fun h' ↦ ⟨hPQ h'.prop, fun y hy hyx ↦ ?_⟩⟩
  · obtain ⟨y, hyx, hy⟩ := h h'.prop
    rwa [((h'.le_of_le (hPQ hy)) hyx).antisymm hyx]
  obtain ⟨z, hzy, hz⟩ := h hy
  exact (h'.le_of_le hz (hzy.trans hyx)).trans hzy

end PartialOrder

section LinearOrder

variable [LinearOrder α] {i j : ι} {Q : ι → Prop} {f : ι → α}

@[to_dual]
/-
**Minimal.le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Minimal.le (h : Minimal P x) (hy : P y) : x <= y
参数：h : Minimal P x；hy : P y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Minimal.not_lt`：Minimal.not_lt (h : Minimal P x) (hy : P y) : ¬(y < x)
-/
theorem Minimal.le (h : Minimal P x) (hy : P y) : x ≤ y :=
  le_of_not_gt (h.not_lt hy)

@[to_dual]
/-
**MinimalFor.le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MinimalFor.le (h : MinimalFor Q f i) (hj : Q j) : f i <= f j
参数：h : MinimalFor Q f i；hj : Q j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `MinimalFor.not_lt`：MinimalFor.not_lt (h : MinimalFor Q f i) (hj : Q j) :
 ¬(f j < f i)
-/
theorem MinimalFor.le (h : MinimalFor Q f i) (hj : Q j) : f i ≤ f j :=
  le_of_not_gt (h.not_lt hj)

end LinearOrder

section Subset

variable {P : Set α → Prop} {s t : Set α}

/-
**Minimal.eq_of_superset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Minimal.eq_of_superset (h : Minimal P s) (ht : P t) (hts : t subseteq s) :
 s = t
参数：h : Minimal P s；ht : P t；hts : t subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Minimal.eq_of_ge`：Minimal.eq_of_ge (hx : Minimal P x) (hy : P y) (hge : 
y <= x) : x = y
-/
theorem Minimal.eq_of_superset (h : Minimal P s) (ht : P t) (hts : t ⊆ s) : s = t :=
  h.eq_of_ge ht hts
/-
**Maximal.eq_of_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Maximal.eq_of_subset (h : Maximal P s) (ht : P t) (hst : s subseteq t) : s
 = t
参数：h : Maximal P s；ht : P t；hst : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Maximal.eq_of_le`：∀ {α : Type u_2} {P : α → Prop} {x y : α} [inst : Part
ialOrder α], Maximal P x → P y → x ≤ y → x = y
-/
theorem Maximal.eq_of_subset (h : Maximal P s) (ht : P t) (hst : s ⊆ t) : s = t :=
  h.eq_of_le ht hst
/-
**Minimal.eq_of_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Minimal.eq_of_subset (h : Minimal P s) (ht : P t) (hts : t subseteq s) : t
 = s
参数：h : Minimal P s；ht : P t；hts : t subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Minimal.eq_of_le`：Minimal.eq_of_le (hx : Minimal P x) (hy : P y) (hle : 
y <= x) : y = x
-/
theorem Minimal.eq_of_subset (h : Minimal P s) (ht : P t) (hts : t ⊆ s) : t = s :=
  h.eq_of_le ht hts
/-
**Maximal.eq_of_superset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Maximal.eq_of_superset (h : Maximal P s) (ht : P t) (hst : s subseteq t) :
 t = s
参数：h : Maximal P s；ht : P t；hst : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Maximal.eq_of_ge`：∀ {α : Type u_2} {P : α → Prop} {x y : α} [inst : Part
ialOrder α], Maximal P x → P y → x ≤ y → y = x
-/
theorem Maximal.eq_of_superset (h : Maximal P s) (ht : P t) (hst : s ⊆ t) : t = s :=
  h.eq_of_ge ht hst
/-
**minimal_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minimal_subset_iff : Minimal P s ↔ P s ∧ forall ⦃t⦄, P t -> t subseteq s -
> s = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minimal_iff`：minimal_iff : Minimal P x ↔ P x ∧ forall ⦃y⦄, P y -> y <= x
 -> x = y
-/
theorem minimal_subset_iff : Minimal P s ↔ P s ∧ ∀ ⦃t⦄, P t → t ⊆ s → s = t :=
  _root_.minimal_iff
/-
**maximal_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：maximal_subset_iff : Maximal P s ↔ P s ∧ forall ⦃t⦄, P t -> s subseteq t -
> s = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `maximal_iff`：∀ {α : Type u_2} {P : α → Prop} {x : α} [inst : PartialOrde
r α], Maximal P x ↔ P x ∧ ∀ ⦃y : α⦄, P y → x ≤ y → x = y
-/
theorem maximal_subset_iff : Maximal P s ↔ P s ∧ ∀ ⦃t⦄, P t → s ⊆ t → s = t :=
  _root_.maximal_iff
/-
**minimal_subset_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minimal_subset_iff' : Minimal P s ↔ P s ∧ forall ⦃t⦄, P t -> t subseteq s 
-> s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem minimal_subset_iff' : Minimal P s ↔ P s ∧ ∀ ⦃t⦄, P t → t ⊆ s → s ⊆ t :=
  Iff.rfl
/-
**maximal_subset_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：maximal_subset_iff' : Maximal P s ↔ P s ∧ forall ⦃t⦄, P t -> s subseteq t 
-> t subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem maximal_subset_iff' : Maximal P s ↔ P s ∧ ∀ ⦃t⦄, P t → s ⊆ t → t ⊆ s :=
  Iff.rfl
/-
**not_minimal_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_minimal_subset_iff (hs : P s) : ¬ Minimal P s ↔ exists t, t ⊂ s ∧ P t
参数：hs : P s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_minimal_iff_exists_lt`：not_minimal_iff_exists_lt (hx : P x) : ¬ Mini
mal P x ↔ exists y, y < x ∧ P y
-/
theorem not_minimal_subset_iff (hs : P s) : ¬ Minimal P s ↔ ∃ t, t ⊂ s ∧ P t :=
  not_minimal_iff_exists_lt hs
/-
**not_maximal_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_maximal_subset_iff (hs : P s) : ¬ Maximal P s ↔ exists t, s ⊂ t ∧ P t
参数：hs : P s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_maximal_iff_exists_gt`：∀ {α : Type u_2} {P : α → Prop} {x : α} [inst
 : Preorder α], P x → (¬Maximal P x ↔ ∃ y, x < y ∧ P y)
-/
theorem not_maximal_subset_iff (hs : P s) : ¬ Maximal P s ↔ ∃ t, s ⊂ t ∧ P t :=
  not_maximal_iff_exists_gt hs
/-
**Set.minimal_iff_forall_ssubset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.minimal_iff_forall_ssubset : Minimal P s ↔ P s ∧ forall ⦃t⦄, t ⊂ s -> 
¬ P t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minimal_iff_forall_lt`：minimal_iff_forall_lt : Minimal P x ↔ P x ∧ foral
l ⦃y⦄, y < x -> ¬ P y
-/
theorem Set.minimal_iff_forall_ssubset : Minimal P s ↔ P s ∧ ∀ ⦃t⦄, t ⊂ s → ¬ P t :=
  minimal_iff_forall_lt
/-
**Minimal.not_prop_of_ssubset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Minimal.not_prop_of_ssubset (h : Minimal P s) (ht : t ⊂ s) : ¬ P t
参数：h : Minimal P s；ht : t ⊂ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `minimal_iff_forall_lt`：minimal_iff_forall_lt : Minimal P x ↔ P x ∧ foral
l ⦃y⦄, y < x -> ¬ P y
-/
theorem Minimal.not_prop_of_ssubset (h : Minimal P s) (ht : t ⊂ s) : ¬ P t :=
  (minimal_iff_forall_lt.1 h).2 ht
/-
**Minimal.not_ssubset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Minimal.not_ssubset (h : Minimal P s) (ht : P t) : ¬ t ⊂ s
参数：h : Minimal P s；ht : P t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Minimal.not_lt`：Minimal.not_lt (h : Minimal P x) (hy : P y) : ¬(y < x)
-/
theorem Minimal.not_ssubset (h : Minimal P s) (ht : P t) : ¬ t ⊂ s :=
  h.not_lt ht
/-
**Maximal.mem_of_prop_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Maximal.mem_of_prop_insert (h : Maximal P s) (hx : P (insert x s)) : x in 
s
参数：h : Maximal P s；hx : P (insert x s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Maximal.eq_of_subset`：Maximal.eq_of_subset (h : Maximal P s) (ht : P t) 
(hst : s subseteq t) : s = t
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
-/
theorem Maximal.mem_of_prop_insert (h : Maximal P s) (hx : P (insert x s)) : x ∈ s :=
  h.eq_of_subset hx (subset_insert _ _) ▸ mem_insert ..
/-
**Minimal.notMem_of_prop_sdiff_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Minimal.notMem_of_prop_sdiff_singleton (h : Minimal P s) (hx : P (s \ {x})
) : x ∉ s
参数：h : Minimal P s；hx : P (s \ {x})。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Minimal.eq_of_superset`：Minimal.eq_of_superset (h : Minimal P s) (ht : P
 t) (hts : t subseteq s) : s = t
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
theorem Minimal.notMem_of_prop_sdiff_singleton (h : Minimal P s) (hx : P (s \ {x})) : x ∉ s :=
  fun hxs ↦ ((h.eq_of_superset hx sdiff_subset).subset hxs).2 rfl

@[deprecated (since := "2026-06-03")]
alias Minimal.notMem_of_prop_diff_singleton := Minimal.notMem_of_prop_sdiff_singleton
/-
**Set.minimal_iff_forall_sdiff_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.minimal_iff_forall_sdiff_singleton (hP : forall ⦃s t⦄, P t -> t subset
eq s -> P s) : Minimal P s ↔ P s ∧ forall x in s, ¬ P (s \ {x})
参数：hP : forall ⦃s t⦄, P t -> t subseteq s -> P s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Minimal.notMem_of_prop_sdiff_singleton`：Minimal.notMem_of_prop_sdiff_sin
gleton (h : Minimal P s) (hx : P (s \ {x})) : x ∉ s
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Set.subset_sdiff_singleton`：subset_sdiff_singleton (h : s subseteq t) (h
a : a ∉ s) : s subseteq t \ {a}
-/
theorem Set.minimal_iff_forall_sdiff_singleton (hP : ∀ ⦃s t⦄, P t → t ⊆ s → P s) :
    Minimal P s ↔ P s ∧ ∀ x ∈ s, ¬ P (s \ {x}) :=
  ⟨fun h ↦ ⟨h.1, fun _ hx hP ↦ h.notMem_of_prop_sdiff_singleton hP hx⟩,
    fun h ↦ ⟨h.1, fun _ ht hts x hxs ↦ by_contra fun hxt ↦
      h.2 x hxs (hP ht <| subset_sdiff_singleton hts hxt)⟩⟩

@[deprecated (since := "2026-06-03")]
alias Set.minimal_iff_forall_diff_singleton := Set.minimal_iff_forall_sdiff_singleton
/-
**Set.exists_sdiff_singleton_of_not_minimal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.exists_sdiff_singleton_of_not_minimal (hP : forall ⦃s t⦄, P t -> t sub
seteq s -> P s) (hs : P s) (h : ¬ Minimal P s) : exists x in s, P (s \ {x})
参数：hP : forall ⦃s t⦄, P t -> t subseteq s -> P s；hs : P s；h : ¬ Minimal P s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.minimal_iff_forall_sdiff_singleton`：Set.minimal_iff_forall_sdiff_sin
gleton (hP : forall ⦃s t⦄, P t -> t subseteq s -> P s) : Minimal P s ↔ P s ∧ for
all x in s, ¬ P (s \ {x})
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem Set.exists_sdiff_singleton_of_not_minimal (hP : ∀ ⦃s t⦄, P t → t ⊆ s → P s) (hs : P s)
    (h : ¬ Minimal P s) : ∃ x ∈ s, P (s \ {x}) := by
  simpa [Set.minimal_iff_forall_sdiff_singleton hP, hs] using h

@[deprecated (since := "2026-06-03")]
alias Set.exists_diff_singleton_of_not_minimal := Set.exists_sdiff_singleton_of_not_minimal
/-
**Set.maximal_iff_forall_ssuperset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.maximal_iff_forall_ssuperset : Maximal P s ↔ P s ∧ forall ⦃t⦄, s ⊂ t -
> ¬ P t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `maximal_iff_forall_gt`：∀ {α : Type u_2} {P : α → Prop} {x : α} [inst : P
reorder α], Maximal P x ↔ P x ∧ ∀ ⦃y : α⦄, x < y → ¬P y
-/
theorem Set.maximal_iff_forall_ssuperset : Maximal P s ↔ P s ∧ ∀ ⦃t⦄, s ⊂ t → ¬ P t :=
  maximal_iff_forall_gt
/-
**Maximal.not_prop_of_ssuperset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Maximal.not_prop_of_ssuperset (h : Maximal P s) (ht : s ⊂ t) : ¬ P t
参数：h : Maximal P s；ht : s ⊂ t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `maximal_iff_forall_gt`：∀ {α : Type u_2} {P : α → Prop} {x : α} [inst : P
reorder α], Maximal P x ↔ P x ∧ ∀ ⦃y : α⦄, x < y → ¬P y
-/
theorem Maximal.not_prop_of_ssuperset (h : Maximal P s) (ht : s ⊂ t) : ¬ P t :=
  (maximal_iff_forall_gt.1 h).2 ht
/-
**Maximal.not_ssuperset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Maximal.not_ssuperset (h : Maximal P s) (ht : P t) : ¬ s ⊂ t
参数：h : Maximal P s；ht : P t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Maximal.not_gt`：∀ {α : Type u_2} {P : α → Prop} {x y : α} [inst : Preord
er α], Maximal P x → P y → ¬x < y
-/
theorem Maximal.not_ssuperset (h : Maximal P s) (ht : P t) : ¬ s ⊂ t :=
  h.not_gt ht
/-
**Set.maximal_iff_forall_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.maximal_iff_forall_insert (hP : forall ⦃s t⦄, P t -> s subseteq t -> P
 s) : Maximal P s ↔ P s ∧ forall x ∉ s, ¬ P (insert x s)
参数：hP : forall ⦃s t⦄, P t -> s subseteq t -> P s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Maximal.mem_of_prop_insert`：Maximal.mem_of_prop_insert (h : Maximal P s)
 (hx : P (insert x s)) : x in s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
-/
theorem Set.maximal_iff_forall_insert (hP : ∀ ⦃s t⦄, P t → s ⊆ t → P s) :
    Maximal P s ↔ P s ∧ ∀ x ∉ s, ¬ P (insert x s) := by
  simp only [not_imp_not]
  exact ⟨fun h ↦ ⟨h.1, fun x ↦ h.mem_of_prop_insert⟩,
    fun h ↦ ⟨h.1, fun t ht hst x hxt ↦ h.2 x (hP ht <| insert_subset hxt hst)⟩⟩
/-
**Set.exists_insert_of_not_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.exists_insert_of_not_maximal (hP : forall ⦃s t⦄, P t -> s subseteq t -
> P s) (hs : P s) (h : ¬ Maximal P s) : exists x ∉ s, P (insert x s)
参数：hP : forall ⦃s t⦄, P t -> s subseteq t -> P s；hs : P s；h : ¬ Maximal P s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.maximal_iff_forall_insert`：Set.maximal_iff_forall_insert (hP : foral
l ⦃s t⦄, P t -> s subseteq t -> P s) : Maximal P s ↔ P s ∧ forall x ∉ s, ¬ P (in
sert x s)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem Set.exists_insert_of_not_maximal (hP : ∀ ⦃s t⦄, P t → s ⊆ t → P s) (hs : P s)
    (h : ¬ Maximal P s) : ∃ x ∉ s, P (insert x s) := by
  simpa [Set.maximal_iff_forall_insert hP, hs] using h

/- TODO : generalize `minimal_iff_forall_sdiff_singleton` and `maximal_iff_forall_insert`
to `IsStronglyCoatomic`/`IsStronglyAtomic` orders. -/

end Subset

section Set

variable {s t : Set α}
section Preorder

variable [Preorder α]

@[to_dual]
/-
**setOfPred_minimal_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：setOfPred_minimal_subset (s : Set α) : {x | Minimal (· in s) x} subseteq s
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.sep_subset`：sep_subset (s : Set α) (p : α -> Prop) : { x in s | p x 
} subseteq s
-/
theorem setOfPred_minimal_subset (s : Set α) : {x | Minimal (· ∈ s) x} ⊆ s :=
  sep_subset ..

@[deprecated (since := "2026-07-09")] alias setOf_minimal_subset := setOfPred_minimal_subset
@[deprecated (since := "2026-07-09")] alias setOf_maximal_subset := setOfPred_maximal_subset

@[to_dual]
/-
**Set.Subsingleton.minimal_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Subsingleton.minimal_mem_iff (h : s.Subsingleton) : Minimal (· in s) x
 ↔ x in s
参数：h : s.Subsingleton。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.eq_empty_or_singleton`：∀ {α : Type u} {s : Set α}, s.Su
bsingleton → s = ∅ ∨ ∃ x, s = {x}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Set.Subsingleton.minimal_mem_iff (h : s.Subsingleton) : Minimal (· ∈ s) x ↔ x ∈ s := by
  obtain (rfl | ⟨x, rfl⟩) := h.eq_empty_or_singleton <;> simp

@[to_dual]
/-
**IsLeast.minimal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLeast.minimal (h : IsLeast s x) : Minimal (· in s) x
参数：h : IsLeast s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsLeast.minimal (h : IsLeast s x) : Minimal (· ∈ s) x :=
  ⟨h.1, fun _b hb _ ↦ h.2 hb⟩

end Preorder

section PartialOrder

variable [PartialOrder α]

@[to_dual]
/-
**IsLeast.minimal_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLeast.minimal_iff (h : IsLeast s a) : Minimal (· in s) x ↔ x = a
参数：h : IsLeast s a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Minimal.eq_of_ge`：Minimal.eq_of_ge (hx : Minimal P x) (hy : P y) (hge : 
y <= x) : x = y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Minimal.prop`：Minimal.prop (h : Minimal P x) : P x
· 使用定理 `IsLeast.minimal`：IsLeast.minimal (h : IsLeast s x) : Minimal (· in s) x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsLeast.minimal_iff (h : IsLeast s a) : Minimal (· ∈ s) x ↔ x = a :=
  ⟨fun h' ↦ h'.eq_of_ge h.1 (h.2 h'.prop), fun h' ↦ h' ▸ h.minimal⟩

end PartialOrder

end Set

section Image

variable [Preorder α] [Preorder β] {s : Set α} {t : Set β}
section Function

variable {f : α → β}

-- TODO: the names in this section are all wrong
@[to_dual (reorder := hf (x y, 3 4))]
/-
**minimal_mem_image_monotone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minimal_mem_image_monotone (hf : forall ⦃x y⦄, x in s -> y in s -> (f x <=
 f y ↔ x <= y)) (hx : Minimal (· in s) x) : Minimal (· in f '' s) (f x)
参数：hf : forall ⦃x y⦄, x in s -> y in s -> (f x <= f y ↔ x <= y)；hx : Minimal (· 
in s) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用引理 `Minimal.prop`：Minimal.prop (h : Minimal P x) : P x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Minimal.le_of_le`：Minimal.le_of_le (h : Minimal P x) (hy : P y) (hle : y
 <= x) : x <= y
-/
theorem minimal_mem_image_monotone (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ x ≤ y))
    (hx : Minimal (· ∈ s) x) : Minimal (· ∈ f '' s) (f x) := by
  refine ⟨mem_image_of_mem f hx.prop, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [hf hx.prop hy, hf hy hx.prop]
  exact hx.le_of_le hy

@[to_dual (reorder := hf (x y, 3 4))]
/-
**minimal_mem_image_monotone_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minimal_mem_image_monotone_iff (ha : a in s) (hf : forall ⦃x y⦄, x in s ->
 y in s -> (f x <= f y ↔ x <= y)) : Minimal (· in f '' s) (f a) ↔ Minimal (· in 
s) a
参数：ha : a in s；hf : forall ⦃x y⦄, x in s -> y in s -> (f x <= f y ↔ x <= y)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Minimal.le_of_le`：Minimal.le_of_le (h : Minimal P x) (hy : P y) (hle : y
 <= x) : x <= y
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `minimal_mem_image_monotone`：minimal_mem_image_monotone (hf : forall ⦃x y
⦄, x in s -> y in s -> (f x <= f y ↔ x <= y)) (hx : Minimal (· in s) x) : Minima
l (· in f '' s) …
-/
theorem minimal_mem_image_monotone_iff (ha : a ∈ s)
    (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ x ≤ y)) :
    Minimal (· ∈ f '' s) (f a) ↔ Minimal (· ∈ s) a := by
  refine ⟨fun h ↦ ⟨ha, fun y hys ↦ ?_⟩, minimal_mem_image_monotone hf⟩
  rw [← hf ha hys, ← hf hys ha]
  exact h.le_of_le (mem_image_of_mem f hys)

@[to_dual (reorder := hf (x y, 3 4))]
/-
**minimal_mem_image_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minimal_mem_image_antitone (hf : forall ⦃x y⦄, x in s -> y in s -> (f x <=
 f y ↔ y <= x)) (hx : Minimal (· in s) x) : Maximal (· in f '' s) (f x)
参数：hf : forall ⦃x y⦄, x in s -> y in s -> (f x <= f y ↔ y <= x)；hx : Minimal (· 
in s) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minimal_mem_image_monotone`：minimal_mem_image_monotone (hf : forall ⦃x y
⦄, x in s -> y in s -> (f x <= f y ↔ x <= y)) (hx : Minimal (· in s) x) : Minima
l (· in f '' s) …
-/
theorem minimal_mem_image_antitone (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ y ≤ x))
    (hx : Minimal (· ∈ s) x) : Maximal (· ∈ f '' s) (f x) :=
  minimal_mem_image_monotone (β := βᵒᵈ) (fun _ _ h h' ↦ hf h' h) hx

@[to_dual (reorder := hf (x y, 3 4))]
/-
**minimal_mem_image_antitone_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minimal_mem_image_antitone_iff (ha : a in s) (hf : forall ⦃x y⦄, x in s ->
 y in s -> (f x <= f y ↔ y <= x)) : Minimal (· in f '' s) (f a) ↔ Maximal (· in 
s) a
参数：ha : a in s；hf : forall ⦃x y⦄, x in s -> y in s -> (f x <= f y ↔ y <= x)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `maximal_mem_image_monotone_iff`：∀ {α : Type u_2} {β : Type u_3} {a : α} 
[inst : Preorder α] [inst_1 : Preorder β] {s : Set α} {f : α → β},   a ∈ s →    
 (∀ ⦃y x : α⦄, y ∈ s…
-/
theorem minimal_mem_image_antitone_iff (ha : a ∈ s)
    (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ y ≤ x)) :
    Minimal (· ∈ f '' s) (f a) ↔ Maximal (· ∈ s) a :=
  maximal_mem_image_monotone_iff (β := βᵒᵈ) ha (fun _ _ h h' ↦ hf h' h)

@[to_dual (reorder := hf (x y, 3 4))]
/-
**image_monotone_setOfPred_minimal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_monotone_setOfPred_minimal (hf : forall ⦃x y⦄, P x -> P y -> (f x <=
 f y ↔ x <= y)) : f '' {x | Minimal P x} = {x | Minimal (exists x₀, P x₀ ∧ f x₀ 
= ·) x}
参数：hf : forall ⦃x y⦄, P x -> P y -> (f x <= f y ↔ x <= y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `minimal_mem_image_monotone_iff`：minimal_mem_image_monotone_iff (ha : a i
n s) (hf : forall ⦃x y⦄, x in s -> y in s -> (f x <= f y ↔ x <= y)) : Minimal (·
 in f '' s) (f a) ↔ …
· 使用引理 `Minimal.prop`：Minimal.prop (h : Minimal P x) : P x
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem image_monotone_setOfPred_minimal (hf : ∀ ⦃x y⦄, P x → P y → (f x ≤ f y ↔ x ≤ y)) :
    f '' {x | Minimal P x} = {x | Minimal (∃ x₀, P x₀ ∧ f x₀ = ·) x} := by
  refine Set.ext fun x ↦ ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨x, (hx : Minimal _ x), rfl⟩
    exact (minimal_mem_image_monotone_iff hx.prop hf).2 hx
  obtain ⟨y, hy, rfl⟩ := (mem_ofPred_eq ▸ h).prop
  exact mem_image_of_mem _ <| (minimal_mem_image_monotone_iff (s := Set.ofPred P) hy hf).1 h

@[deprecated (since := "2026-07-09")]
alias image_monotone_setOf_minimal := image_monotone_setOfPred_minimal

@[deprecated (since := "2026-07-09")]
alias image_monotone_setOf_maximal := image_monotone_setOfPred_maximal

@[to_dual (reorder := hf (x y, 3 4))]
/-
**image_antitone_setOfPred_minimal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_antitone_setOfPred_minimal (hf : forall ⦃x y⦄, P x -> P y -> (f x <=
 f y ↔ y <= x)) : f '' {x | Minimal P x} = {x | Maximal (exists x₀, P x₀ ∧ f x₀ 
= ·) x}
参数：hf : forall ⦃x y⦄, P x -> P y -> (f x <= f y ↔ y <= x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `image_monotone_setOfPred_minimal`：image_monotone_setOfPred_minimal (hf :
 forall ⦃x y⦄, P x -> P y -> (f x <= f y ↔ x <= y)) : f '' {x | Minimal P x} = {
x | Minimal (exists x₀…
-/
theorem image_antitone_setOfPred_minimal (hf : ∀ ⦃x y⦄, P x → P y → (f x ≤ f y ↔ y ≤ x)) :
    f '' {x | Minimal P x} = {x | Maximal (∃ x₀, P x₀ ∧ f x₀ = ·) x} :=
  image_monotone_setOfPred_minimal (β := βᵒᵈ) (fun _ _ hx hy ↦ hf hy hx)

@[deprecated (since := "2026-07-09")]
alias image_antitone_setOf_minimal := image_antitone_setOfPred_minimal

@[deprecated (since := "2026-07-09")]
alias image_antitone_setOf_maximal := image_antitone_setOfPred_maximal

@[to_dual (reorder := hf (x y, 3 4))]
/-
**image_monotone_setOfPred_minimal_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_monotone_setOfPred_minimal_mem (hf : forall ⦃x y⦄, x in s -> y in s 
-> (f x <= f y ↔ x <= y)) : f '' {x | Minimal (· in s) x} = {x | Minimal (· in f
 '' s) x}
参数：hf : forall ⦃x y⦄, x in s -> y in s -> (f x <= f y ↔ x <= y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `image_monotone_setOfPred_minimal`：image_monotone_setOfPred_minimal (hf :
 forall ⦃x y⦄, P x -> P y -> (f x <= f y ↔ x <= y)) : f '' {x | Minimal P x} = {
x | Minimal (exists x₀…
-/
theorem image_monotone_setOfPred_minimal_mem (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ x ≤ y)) :
    f '' {x | Minimal (· ∈ s) x} = {x | Minimal (· ∈ f '' s) x} :=
  image_monotone_setOfPred_minimal hf

@[deprecated (since := "2026-07-09")]
alias image_monotone_setOf_minimal_mem := image_monotone_setOfPred_minimal_mem

@[deprecated (since := "2026-07-09")]
alias image_monotone_setOf_maximal_mem := image_monotone_setOfPred_maximal_mem

@[to_dual (reorder := hf (x y, 3 4))]
/-
**image_antitone_setOfPred_minimal_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_antitone_setOfPred_minimal_mem (hf : forall ⦃x y⦄, x in s -> y in s 
-> (f x <= f y ↔ y <= x)) : f '' {x | Minimal (· in s) x} = {x | Maximal (· in f
 '' s) x}
参数：hf : forall ⦃x y⦄, x in s -> y in s -> (f x <= f y ↔ y <= x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `image_antitone_setOfPred_minimal`：image_antitone_setOfPred_minimal (hf :
 forall ⦃x y⦄, P x -> P y -> (f x <= f y ↔ y <= x)) : f '' {x | Minimal P x} = {
x | Maximal (exists x₀…
-/
theorem image_antitone_setOfPred_minimal_mem (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ y ≤ x)) :
    f '' {x | Minimal (· ∈ s) x} = {x | Maximal (· ∈ f '' s) x} :=
  image_antitone_setOfPred_minimal hf

@[deprecated (since := "2026-07-09")]
alias image_antitone_setOf_minimal_mem := image_antitone_setOfPred_minimal_mem

@[deprecated (since := "2026-07-09")]
alias image_antitone_setOf_maximal_mem := image_antitone_setOfPred_maximal_mem

end Function

namespace OrderEmbedding

variable {f : α ↪o β} {t : Set β}

@[to_dual]
/-
**OrderEmbedding.minimal_mem_image** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：minimal_mem_image (f : α ↪o β) (hx : Minimal (· in s) x) : Minimal (· in f
 '' s) (f x)
参数：f : α ↪o β；hx : Minimal (· in s) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minimal_mem_image_monotone`：minimal_mem_image_monotone (hf : forall ⦃x y
⦄, x in s -> y in s -> (f x <= f y ↔ x <= y)) (hx : Minimal (· in s) x) : Minima
l (· in f '' s) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderEmbedding.le_iff_le`：le_iff_le {a b} : f a <= f b ↔ a <= b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem minimal_mem_image (f : α ↪o β) (hx : Minimal (· ∈ s) x) : Minimal (· ∈ f '' s) (f x) :=
  _root_.minimal_mem_image_monotone (by simp [f.le_iff_le]) hx

@[to_dual]
/-
**OrderEmbedding.minimal_mem_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding
`。
形式化陈述：minimal_mem_image_iff (ha : a in s) : Minimal (· in f '' s) (f a) ↔ Minima
l (· in s) a
参数：ha : a in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minimal_mem_image_monotone_iff`：minimal_mem_image_monotone_iff (ha : a i
n s) (hf : forall ⦃x y⦄, x in s -> y in s -> (f x <= f y ↔ x <= y)) : Minimal (·
 in f '' s) (f a) ↔ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderEmbedding.le_iff_le`：le_iff_le {a b} : f a <= f b ↔ a <= b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem minimal_mem_image_iff (ha : a ∈ s) : Minimal (· ∈ f '' s) (f a) ↔ Minimal (· ∈ s) a :=
  _root_.minimal_mem_image_monotone_iff ha (by simp [f.le_iff_le])

@[to_dual]
/-
**OrderEmbedding.minimal_apply_mem_inter_range_iff** 是 Mathlib 中的一个定理，位于命名空间 `Or
derEmbedding`。
形式化陈述：minimal_apply_mem_inter_range_iff : Minimal (· in t inter range f) (f x) ↔
 Minimal (fun x => f x in t) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Minimal.prop`：Minimal.prop (h : Minimal P x) : P x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderEmbedding.le_iff_le`：le_iff_le {a b} : f a <= f b ↔ a <= b
· 使用引理 `Minimal.le_of_le`：Minimal.le_of_le (h : Minimal P x) (hy : P y) (hle : y
 <= x) : x <= y
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem minimal_apply_mem_inter_range_iff :
    Minimal (· ∈ t ∩ range f) (f x) ↔ Minimal (fun x ↦ f x ∈ t) x := by
  refine ⟨fun h ↦ ⟨h.prop.1, fun y hy ↦ ?_⟩, fun h ↦ ⟨⟨h.prop, mem_range_self x⟩, ?_⟩⟩
  · rw [← f.le_iff_le, ← f.le_iff_le]
    exact h.le_of_le ⟨hy, mem_range_self y⟩
  rintro _ ⟨hyt, ⟨y, rfl⟩⟩
  simp_rw [f.le_iff_le]
  exact h.le_of_le hyt

@[to_dual]
/-
**OrderEmbedding.minimal_apply_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding
`。
形式化陈述：minimal_apply_mem_iff (ht : t subseteq Set.range f) : Minimal (· in t) (f 
x) ↔ Minimal (fun x => f x in t) x
参数：ht : t subseteq Set.range f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderEmbedding.minimal_apply_mem_inter_range_iff`：minimal_apply_mem_inte
r_range_iff : Minimal (· in t inter range f) (f x) ↔ Minimal (fun x => f x in t)
 x
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem minimal_apply_mem_iff (ht : t ⊆ Set.range f) :
    Minimal (· ∈ t) (f x) ↔ Minimal (fun x ↦ f x ∈ t) x := by
  rw [← f.minimal_apply_mem_inter_range_iff, inter_eq_self_of_subset_left ht]

@[deprecated (since := "2026-04-07")] alias maximal_apply_iff := maximal_apply_mem_iff
/-
**OrderEmbedding.image_setOfPred_minimal** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbeddi
ng`。
形式化陈述：image_setOfPred_minimal : f '' {x | Minimal (· in s) x} = {x | Minimal (· 
in f '' s) x}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `image_monotone_setOfPred_minimal`：image_monotone_setOfPred_minimal (hf :
 forall ⦃x y⦄, P x -> P y -> (f x <= f y ↔ x <= y)) : f '' {x | Minimal P x} = {
x | Minimal (exists x₀…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderEmbedding.le_iff_le`：le_iff_le {a b} : f a <= f b ↔ a <= b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem image_setOfPred_minimal : f '' {x | Minimal (· ∈ s) x} = {x | Minimal (· ∈ f '' s) x} :=
  _root_.image_monotone_setOfPred_minimal (by simp [f.le_iff_le])

@[deprecated (since := "2026-07-09")]
alias image_setOf_minimal := image_setOfPred_minimal

@[to_dual]
/-
**OrderEmbedding.inter_preimage_setOfPred_minimal_eq_of_subset** 是 Mathlib 中的一个定
理，位于命名空间 `OrderEmbedding`。
形式化陈述：inter_preimage_setOfPred_minimal_eq_of_subset (hts : t subseteq f '' s) : 
x in s inter f ⁻¹' {y | Minimal (· in t) y} ↔ Minimal (· in s inter f ⁻¹' t) x
参数：hts : t subseteq f '' s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `OrderEmbedding.minimal_apply_mem_iff`：minimal_apply_mem_iff (ht : t subs
eteq Set.range f) : Minimal (· in t) (f x) ↔ Minimal (fun x => f x in t) x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `minimal_and_iff_left_of_imp`：minimal_and_iff_left_of_imp (hPQ : forall ⦃
x⦄, P x -> Q x) : Minimal (fun x => Q x ∧ P x) x ↔ Q x ∧ (Minimal P x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem inter_preimage_setOfPred_minimal_eq_of_subset (hts : t ⊆ f '' s) :
    x ∈ s ∩ f ⁻¹' {y | Minimal (· ∈ t) y} ↔ Minimal (· ∈ s ∩ f ⁻¹' t) x := by
  simp_rw [mem_inter_iff, preimage_ofPred_eq, mem_ofPred_eq, mem_preimage,
    f.minimal_apply_mem_iff (hts.trans (image_subset_range _ _)),
    minimal_and_iff_left_of_imp (fun _ hx ↦ f.injective.mem_set_image.1 <| hts hx)]

@[deprecated (since := "2026-07-09")]
alias inter_preimage_setOf_minimal_eq_of_subset := inter_preimage_setOfPred_minimal_eq_of_subset

@[deprecated (since := "2026-07-09")]
alias inter_preimage_setOf_maximal_eq_of_subset := inter_preimage_setOfPred_maximal_eq_of_subset

end OrderEmbedding

namespace OrderIso

@[to_dual]
/-
**OrderIso.image_setOfPred_minimal** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：image_setOfPred_minimal (f : α ≃o β) (P : α -> Prop) : f '' {x | Minimal P
 x} = {x | Minimal (fun x => P (f.symm x)) x}
参数：f : α ≃o β；P : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `image_monotone_setOfPred_minimal`：image_monotone_setOfPred_minimal (hf :
 forall ⦃x y⦄, P x -> P y -> (f x <= f y ↔ x <= y)) : f '' {x | Minimal P x} = {
x | Minimal (exists x₀…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `OrderIso.le_iff_le`：le_iff_le (e : α ≃o β) {x y : α} : e x <= e y ↔ x <=
 y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem image_setOfPred_minimal (f : α ≃o β) (P : α → Prop) :
    f '' {x | Minimal P x} = {x | Minimal (fun x ↦ P (f.symm x)) x} := by
  convert! _root_.image_monotone_setOfPred_minimal (f := f) (by simp [f.le_iff_le])
  aesop

@[deprecated (since := "2026-07-09")]
alias image_setOf_minimal := image_setOfPred_minimal
@[deprecated (since := "2026-07-09")]
alias image_setOf_maximal := image_setOfPred_maximal

@[to_dual]
/-
**OrderIso.map_minimal_mem** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：map_minimal_mem (f : s ≃o t) (hx : Minimal (· in s) x) : Minimal (· in t) 
(f ⟨x, hx.prop⟩)
参数：f : s ≃o t；hx : Minimal (· in s) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Minimal.prop`：Minimal.prop (h : Minimal P x) : P x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EquivLike.range_comp`：∀ {ι : Sort u_1} {ι' : Sort u_2} {E : Type u_3} [i
nst : EquivLike E ι ι'] {α : Type u_4} (f : ι' → α) (e : E),   Set.range (f ∘ ⇑e
) = Set.ra…
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `OrderEmbedding.minimal_mem_image`：minimal_mem_image (f : α ↪o β) (hx : M
inimal (· in s) x) : Minimal (· in f '' s) (f x)
-/
theorem map_minimal_mem (f : s ≃o t) (hx : Minimal (· ∈ s) x) :
    Minimal (· ∈ t) (f ⟨x, hx.prop⟩) := by
  simpa only [show t = range (Subtype.val ∘ f) by simp, mem_univ, minimal_true_subtype, hx,
    true_imp_iff, image_univ] using! OrderEmbedding.minimal_mem_image
    (f.toOrderEmbedding.trans (OrderEmbedding.subtype (· ∈ t))) (s := univ) (x := ⟨x, hx.prop⟩)

/-- If two sets are order isomorphic, their minimals are also order isomorphic. -/
/-
**OrderIso.mapSetOfPredMinimal** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：mapSetOfPredMinimal (f : s ≃o t) : {x | Minimal (· in s) x} ≃o {x | Minima
l (· in t) x} where toFun x
参数：f : s ≃o t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If two sets are order isomorphic, their minimals are also order isomorphic.
-/
def mapSetOfPredMinimal (f : s ≃o t) : {x | Minimal (· ∈ s) x} ≃o {x | Minimal (· ∈ t) x} where
  toFun x := ⟨f ⟨x, x.2.1⟩, f.map_minimal_mem x.2⟩
  invFun x := ⟨f.symm ⟨x, x.2.1⟩, f.symm.map_minimal_mem x.2⟩
  left_inv x := Subtype.ext (congr_arg Subtype.val <| f.left_inv ⟨x, x.2.1⟩ :)
  right_inv x := Subtype.ext (congr_arg Subtype.val <| f.right_inv ⟨x, x.2.1⟩ :)
  map_rel_iff' := f.map_rel_iff

@[deprecated (since := "2026-07-28")] alias mapSetOfMinimal := mapSetOfPredMinimal

/-- If two sets are order isomorphic, their maximals are also order isomorphic. -/
@[to_dual existing]
/-
**OrderIso.mapSetOfPredMaximal** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：mapSetOfPredMaximal (f : s ≃o t) : {x | Maximal (· in s) x} ≃o {x | Maxima
l (· in t) x} where toFun x
参数：f : s ≃o t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If two sets are order isomorphic, their maximals are also order isomorphic.
-/
def mapSetOfPredMaximal (f : s ≃o t) : {x | Maximal (· ∈ s) x} ≃o {x | Maximal (· ∈ t) x} where
  toFun x := ⟨f ⟨x, x.2.1⟩, f.map_maximal_mem x.2⟩
  invFun x := ⟨f.symm ⟨x, x.2.1⟩, f.symm.map_maximal_mem x.2⟩
  left_inv x := Subtype.ext (congr_arg Subtype.val <| f.left_inv ⟨x, x.2.1⟩ :)
  right_inv x := Subtype.ext (congr_arg Subtype.val <| f.right_inv ⟨x, x.2.1⟩ :)
  map_rel_iff' := f.map_rel_iff

@[deprecated (since := "2026-07-28")] alias mapSetOfMaximal := mapSetOfPredMaximal

/-- If two sets are antitonically order isomorphic, their minimals/maximals are too. -/
@[to_dual /-- If two sets are antitonically order isomorphic, their maximals/minimals are too. -/]
/-
**OrderIso.setOfPredMinimalIsoSetOfPredMaximal** 是 Mathlib 中的一个定义，位于命名空间 `OrderI
so`。
形式化陈述：setOfPredMinimalIsoSetOfPredMaximal (f : s ≃o tᵒᵈ) : {x | Minimal (· in s)
 x} ≃o {x | Maximal (· in t) (ofDual x)} where toFun x
参数：f : s ≃o tᵒᵈ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If two sets are antitonically order isomorphic, their minimals/maximals are too.
-/
def setOfPredMinimalIsoSetOfPredMaximal (f : s ≃o tᵒᵈ) :
    {x | Minimal (· ∈ s) x} ≃o {x | Maximal (· ∈ t) (ofDual x)} where
      toFun x := ⟨(f ⟨x.1, x.2.1⟩).1, ((show s ≃o ofDual ⁻¹' t from f).mapSetOfPredMinimal x).2⟩
      invFun x := ⟨(f.symm ⟨x.1, x.2.1⟩).1,
        ((show ofDual ⁻¹' t ≃o s from f.symm).mapSetOfPredMinimal x).2⟩
      __ := (show s ≃o ofDual ⁻¹' t from f).mapSetOfPredMinimal

@[deprecated (since := "2026-07-09")]
alias setOfMinimalIsoSetOfMaximal := setOfPredMinimalIsoSetOfPredMaximal
@[deprecated (since := "2026-07-09")]
alias setOfMaximalIsoSetOfMinimal := setOfPredMaximalIsoSetOfPredMinimal

end OrderIso

end Image
section Interval

variable [PartialOrder α] {a b : α}

@[to_dual]
/-
**minimal_mem_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minimal_mem_Icc (hab : a <= b) : Minimal (· in Icc a b) x ↔ x = a
参数：hab : a <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minimal_iff_eq`：minimal_iff_eq (hy : P y) (hP : forall ⦃x⦄, P x -> y <= 
x) : Minimal P x ↔ x = y
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem minimal_mem_Icc (hab : a ≤ b) : Minimal (· ∈ Icc a b) x ↔ x = a :=
  minimal_iff_eq ⟨rfl.le, hab⟩ (fun _ ↦ And.left)

@[to_dual]
/-
**minimal_mem_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minimal_mem_Ico (hab : a < b) : Minimal (· in Ico a b) x ↔ x = a
参数：hab : a < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minimal_iff_eq`：minimal_iff_eq (hy : P y) (hP : forall ⦃x⦄, P x -> y <= 
x) : Minimal P x ↔ x = y
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem minimal_mem_Ico (hab : a < b) : Minimal (· ∈ Ico a b) x ↔ x = a :=
  minimal_iff_eq ⟨rfl.le, hab⟩ (fun _ ↦ And.left)

/- Note : The one-sided interval versions of these lemmas are unnecessary,
since `simp` handles them with `maximal_le_iff` and `minimal_ge_iff`. -/

end Interval

