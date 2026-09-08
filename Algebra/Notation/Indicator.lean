/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
module

public import Mathlib.Algebra.Notation.Support
public import Mathlib.Data.Set.Piecewise

/-!
# Indicator function

This file defines the indicator function of a set. More lemmas can be found in
`Mathlib/Algebra/Group/Indicator.lean`.

## Main declarations

- `Set.indicator (s : Set α) (f : α → β) (a : α)` is `f a` if `a ∈ s` and is `0` otherwise.
- `Set.mulIndicator (s : Set α) (f : α → β) (a : α)` is `f a` if `a ∈ s` and is `1` otherwise.

## Implementation note

In mathematics, an indicator function or a characteristic function is a function
used to indicate membership of an element in a set `s`,
having the value `1` for all elements of `s` and the value `0` otherwise.
But since it is usually used to restrict a function to a certain set `s`,
we let the indicator function take the value `f x` for some function `f`, instead of `1`.
If the usual indicator function is needed, just set `f` to be the constant function `fun _ ↦ 1`.

The indicator function is implemented non-computably, to avoid having to pass around `Decidable`
arguments. This is in contrast with the design of `Pi.single` or `Set.piecewise`.

## Tags

indicator, characteristic
-/

@[expose] public section

assert_not_exists Monoid

open Function

variable {α β M N : Type*}

namespace Set
variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

/-- `Set.mulIndicator s f a` is `f a` if `a ∈ s`, `1` otherwise. -/
@[to_additive /-- `Set.indicator s f a` is `f a` if `a ∈ s`, `0` otherwise. -/]
/-
**Set.mulIndicator** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：mulIndicator (s : Set α) (f : α -> M) (x : α) : M
参数：s : Set α；f : α -> M；x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Set.mulIndicator s f a` is `f a` if `a ∈ s`, `1` otherwise.
-/
noncomputable def mulIndicator (s : Set α) (f : α → M) (x : α) : M :=
  haveI := Classical.decPred (· ∈ s)
  if x ∈ s then f x else 1

@[to_additive (attr := simp)]
/-
**Set.piecewise_eq_mulIndicator** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：piecewise_eq_mulIndicator [DecidablePred (· in s)] : s.piecewise f 1 = s.m
ulIndicator f
参数：· in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `if_congr`：if_congr (h_c : P ↔ Q) (h_t : x = u) (h_e : y = v) : ite P x y
 = ite Q u v
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma piecewise_eq_mulIndicator [DecidablePred (· ∈ s)] : s.piecewise f 1 = s.mulIndicator f :=
  funext fun _ => @if_congr _ _ _ _ (id _) _ _ _ _ Iff.rfl rfl rfl

@[to_additive]
/-
**Set.mulIndicator_apply** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_apply (s : Set α) (f : α -> M) (a : α) [Decidable (a in s)] :
 mulIndicator s f a = if a in s then f a else 1
参数：s : Set α；f : α -> M；a : α；a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
-/
lemma mulIndicator_apply (s : Set α) (f : α → M) (a : α) [Decidable (a ∈ s)] :
    mulIndicator s f a = if a ∈ s then f a else 1 := by
  unfold mulIndicator
  congr

@[to_additive (attr := simp)]
/-
**Set.mulIndicator_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_of_mem (h : a in s) (f : α -> M) : mulIndicator s f a = f a
参数：h : a in s；f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma mulIndicator_of_mem (h : a ∈ s) (f : α → M) : mulIndicator s f a = f a := if_pos h

@[to_additive (attr := simp)]
/-
**Set.mulIndicator_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_of_notMem (h : a ∉ s) (f : α -> M) : mulIndicator s f a = 1
参数：h : a ∉ s；f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma mulIndicator_of_notMem (h : a ∉ s) (f : α → M) : mulIndicator s f a = 1 := if_neg h

@[to_additive]
/-
**Set.mulIndicator_eq_one_or_self** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_eq_one_or_self (s : Set α) (f : α -> M) (a : α) : mulIndicato
r s f a = 1 ∨ mulIndicator s f a = f a
参数：s : Set α；f : α -> M；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.mulIndicator_of_mem`：mulIndicator_of_mem (h : a in s) (f : α -> M) :
 mulIndicator s f a = f a
· 使用引理 `Set.mulIndicator_of_notMem`：mulIndicator_of_notMem (h : a ∉ s) (f : α ->
 M) : mulIndicator s f a = 1
-/
lemma mulIndicator_eq_one_or_self (s : Set α) (f : α → M) (a : α) :
    mulIndicator s f a = 1 ∨ mulIndicator s f a = f a := by
  by_cases h : a ∈ s
  · exact Or.inr (mulIndicator_of_mem h f)
  · exact Or.inl (mulIndicator_of_notMem h f)

@[to_additive (attr := simp)]
/-
**Set.mulIndicator_apply_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_apply_eq_self : s.mulIndicator f a = f a ↔ a ∉ s -> f a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `ite_eq_left_iff`：∀ {α : Sort u_1} {p : Prop} [inst : Decidable p] {x y :
 α}, (if p then x else y) = x ↔ ¬p → y = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mulIndicator_apply_eq_self : s.mulIndicator f a = f a ↔ a ∉ s → f a = 1 :=
  letI := Classical.dec (a ∈ s)
  ite_eq_left_iff.trans (by rw [@eq_comm _ (f a)])

@[to_additive (attr := simp)]
/-
**Set.mulIndicator_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_eq_self : s.mulIndicator f = f ↔ mulSupport f subseteq s
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
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mulIndicator_eq_self : s.mulIndicator f = f ↔ mulSupport f ⊆ s := by
  simp only [funext_iff, subset_def, mem_mulSupport, mulIndicator_apply_eq_self, not_imp_comm]

@[to_additive]
/-
**Set.mulIndicator_eq_self_of_superset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_eq_self_of_superset (h1 : s.mulIndicator f = f) (h2 : s subse
teq t) : t.mulIndicator f = f
参数：h1 : s.mulIndicator f = f；h2 : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.mulIndicator_eq_self`：mulIndicator_eq_self : s.mulIndicator f = f ↔ 
mulSupport f subseteq s
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
-/
lemma mulIndicator_eq_self_of_superset (h1 : s.mulIndicator f = f) (h2 : s ⊆ t) :
    t.mulIndicator f = f := by
  rw [mulIndicator_eq_self] at h1 ⊢
  exact Subset.trans h1 h2

@[to_additive (attr := simp)]
/-
**Set.mulIndicator_apply_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_apply_eq_one : mulIndicator s f a = 1 ↔ a in s -> f a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ite_eq_right_iff`：∀ {α : Sort u_1} {p : Prop} [inst : Decidable p] {x y 
: α}, (if p then x else y) = y ↔ p → x = y
-/
lemma mulIndicator_apply_eq_one : mulIndicator s f a = 1 ↔ a ∈ s → f a = 1 :=
  letI := Classical.dec (a ∈ s)
  ite_eq_right_iff

@[to_additive (attr := simp)]
/-
**Set.mulIndicator_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_eq_one : (mulIndicator s f = fun _ => 1) ↔ Disjoint (mulSuppo
rt f) s
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
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mulIndicator_eq_one : (mulIndicator s f = fun _ => 1) ↔ Disjoint (mulSupport f) s := by
  simp only [funext_iff, mulIndicator_apply_eq_one, Set.disjoint_left, mem_mulSupport,
    not_imp_not]

@[to_additive (attr := simp)]
/-
**Set.mulIndicator_eq_one'** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_eq_one' : mulIndicator s f = 1 ↔ Disjoint (mulSupport f) s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.mulIndicator_eq_one`：mulIndicator_eq_one : (mulIndicator s f = fun _
 => 1) ↔ Disjoint (mulSupport f) s
-/
lemma mulIndicator_eq_one' : mulIndicator s f = 1 ↔ Disjoint (mulSupport f) s :=
  mulIndicator_eq_one

@[to_additive]
/-
**Set.mulIndicator_apply_ne_one** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_apply_ne_one {a : α} : s.mulIndicator f a != 1 ↔ a in s inter
 mulSupport f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mulIndicator_apply_ne_one {a : α} : s.mulIndicator f a ≠ 1 ↔ a ∈ s ∩ mulSupport f := by
  simp only [Ne, mulIndicator_apply_eq_one, Classical.not_imp, mem_inter_iff, mem_mulSupport]

@[to_additive (attr := simp)]
/-
**Set.mulSupport_mulIndicator** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulSupport_mulIndicator : Function.mulSupport (s.mulIndicator f) = s inter
 Function.mulSupport f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mulSupport_mulIndicator :
    Function.mulSupport (s.mulIndicator f) = s ∩ Function.mulSupport f :=
  ext fun x => by simp [Function.mem_mulSupport, mulIndicator_apply_eq_one]

/-- If a multiplicative indicator function is not equal to `1` at a point, then that point is in the
set. -/
@[to_additive
/-- If an additive indicator function is not equal to `0` at a point, then that point is in the set.
-/]
/-
**Set.mem_of_mulIndicator_ne_one** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mem_of_mulIndicator_ne_one (h : mulIndicator s f a != 1) : a in s
参数：h : mulIndicator s f a != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用引理 `Set.mulIndicator_of_notMem`：mulIndicator_of_notMem (h : a ∉ s) (f : α ->
 M) : mulIndicator s f a = 1
-/
lemma mem_of_mulIndicator_ne_one (h : mulIndicator s f a ≠ 1) : a ∈ s :=
  not_imp_comm.1 (fun hn => mulIndicator_of_notMem hn f) h

/-- See `Set.eqOn_mulIndicator'` for the version with `sᶜ`. -/
@[to_additive /-- See `Set.eqOn_indicator'` for the version with `sᶜ`. -/]
/-
**Set.eqOn_mulIndicator** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：eqOn_mulIndicator : EqOn (mulIndicator s f) f s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.mulIndicator_of_mem`：mulIndicator_of_mem (h : a in s) (f : α -> M) :
 mulIndicator s f a = f a

--- 原说明 ---
See `Set.eqOn_mulIndicator'` for the version with `sᶜ`.
-/
lemma eqOn_mulIndicator : EqOn (mulIndicator s f) f s := fun _ hx => mulIndicator_of_mem hx f

/-- See `Set.eqOn_mulIndicator` for the version with `s`. -/
@[to_additive /-- See `Set.eqOn_indicator` for the version with `s`. -/]
/-
**Set.eqOn_mulIndicator'** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：eqOn_mulIndicator' : EqOn (mulIndicator s f) 1 sᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.mulIndicator_of_notMem`：mulIndicator_of_notMem (h : a ∉ s) (f : α ->
 M) : mulIndicator s f a = 1

--- 原说明 ---
See `Set.eqOn_mulIndicator` for the version with `s`.
-/
lemma eqOn_mulIndicator' : EqOn (mulIndicator s f) 1 sᶜ :=
  fun _ hx => mulIndicator_of_notMem hx f

@[to_additive]
/-
**Set.mulSupport_mulIndicator_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulSupport_mulIndicator_subset : mulSupport (s.mulIndicator f) subseteq s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Not.imp_symm`：Not.imp_symm : (¬a -> b) -> ¬b -> a
· 使用引理 `Set.mulIndicator_of_notMem`：mulIndicator_of_notMem (h : a ∉ s) (f : α ->
 M) : mulIndicator s f a = 1
-/
lemma mulSupport_mulIndicator_subset : mulSupport (s.mulIndicator f) ⊆ s := fun _ hx =>
  hx.imp_symm fun h => mulIndicator_of_notMem h f

@[to_additive (attr := simp)]
/-
**Set.mulIndicator_mulSupport** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_mulSupport : mulIndicator (mulSupport f) f = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.mulIndicator_eq_self`：mulIndicator_eq_self : s.mulIndicator f = f ↔ 
mulSupport f subseteq s
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
lemma mulIndicator_mulSupport : mulIndicator (mulSupport f) f = f :=
  mulIndicator_eq_self.2 Subset.rfl

@[to_additive (attr := simp)]
/-
**Set.mulIndicator_range_comp** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_range_comp {ι : Sort*} (f : ι -> α) (g : α -> M) : mulIndicat
or (range f) g ∘ f = g ∘ f
参数：f : ι -> α；g : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.piecewise_range_comp`：piecewise_range_comp {ι : Sort*} (f : ι -> α) 
[forall j, Decidable (j in range f)] (g₁ g₂ : α -> β) : (range f).piecewise g₁ g
₂ ∘ f = g₁ ∘ f
-/
lemma mulIndicator_range_comp {ι : Sort*} (f : ι → α) (g : α → M) :
    mulIndicator (range f) g ∘ f = g ∘ f :=
  letI := Classical.decPred (· ∈ range f)
  piecewise_range_comp _ _ _

@[to_additive]
/-
**Set.mulIndicator_congr** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_congr (h : EqOn f g s) : mulIndicator s f = mulIndicator s g
参数：h : EqOn f g s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma mulIndicator_congr (h : EqOn f g s) : mulIndicator s f = mulIndicator s g :=
  funext fun x => by
    simp only [mulIndicator]
    split_ifs with h_1
    · exact h h_1
    rfl

@[to_additive]
/-
**Set.mulIndicator_eq_mulIndicator** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_eq_mulIndicator {t : Set β} {g : β -> M} {b : β} (h1 : a in s
 ↔ b in t) (h2 : f a = g b) : s.mulIndicator f a = t.mulIndicator g b
参数：h1 : a in s ↔ b in t；h2 : f a = g b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.mulIndicator_of_mem`：mulIndicator_of_mem (h : a in s) (f : α -> M) :
 mulIndicator s f a = f a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Set.mulIndicator_of_notMem`：mulIndicator_of_notMem (h : a ∉ s) (f : α ->
 M) : mulIndicator s f a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
-/
lemma mulIndicator_eq_mulIndicator {t : Set β} {g : β → M} {b : β}
    (h1 : a ∈ s ↔ b ∈ t) (h2 : f a = g b) :
    s.mulIndicator f a = t.mulIndicator g b := by
  by_cases a ∈ s <;> simp_all

@[to_additive]
/-
**Set.mulIndicator_const_eq_mulIndicator_const** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_const_eq_mulIndicator_const {t : Set β} {b : β} {c : M} (h : 
a in s ↔ b in t) : s.mulIndicator (fun _ => c) a = t.mulIndicator (fun _ => c) b
参数：h : a in s ↔ b in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.mulIndicator_eq_mulIndicator`：mulIndicator_eq_mulIndicator {t : Set 
β} {g : β -> M} {b : β} (h1 : a in s ↔ b in t) (h2 : f a = g b) : s.mulIndicator
 f a = t.mulIndicator …
-/
lemma mulIndicator_const_eq_mulIndicator_const {t : Set β} {b : β} {c : M} (h : a ∈ s ↔ b ∈ t) :
    s.mulIndicator (fun _ ↦ c) a = t.mulIndicator (fun _ ↦ c) b :=
  mulIndicator_eq_mulIndicator h rfl

@[to_additive (attr := simp)]
/-
**Set.mulIndicator_univ** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_univ (f : α -> M) : mulIndicator (univ : Set α) f = f
参数：f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.mulIndicator_eq_self`：mulIndicator_eq_self : s.mulIndicator f = f ↔ 
mulSupport f subseteq s
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
lemma mulIndicator_univ (f : α → M) : mulIndicator (univ : Set α) f = f :=
  mulIndicator_eq_self.2 <| subset_univ _

@[to_additive (attr := simp)]
/-
**Set.mulIndicator_empty** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_empty (f : α -> M) : mulIndicator (∅ : Set α) f = fun _ => 1
参数：f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.mulIndicator_eq_one`：mulIndicator_eq_one : (mulIndicator s f = fun _
 => 1) ↔ Disjoint (mulSupport f) s
· 使用定理 `Set.disjoint_empty`：∀ {α : Type u} (s : Set α), Disjoint s ∅
-/
lemma mulIndicator_empty (f : α → M) : mulIndicator (∅ : Set α) f = fun _ => 1 :=
  mulIndicator_eq_one.2 <| disjoint_empty _

@[to_additive]
/-
**Set.mulIndicator_empty'** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_empty' (f : α -> M) : mulIndicator (∅ : Set α) f = 1
参数：f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.mulIndicator_empty`：mulIndicator_empty (f : α -> M) : mulIndicator (
∅ : Set α) f = fun _ => 1
-/
lemma mulIndicator_empty' (f : α → M) : mulIndicator (∅ : Set α) f = 1 :=
  mulIndicator_empty f

variable (M)

@[to_additive (attr := simp)]
/-
**Set.mulIndicator_one** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_one (s : Set α) : (mulIndicator s fun _ => (1 : M)) = fun _ =
> (1 : M)
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.mulIndicator_eq_one`：mulIndicator_eq_one : (mulIndicator s f = fun _
 => 1) ↔ Disjoint (mulSupport f) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.mulSupport_fun_one`：mulSupport_fun_one : mulSupport (fun _ => 1
 : ι -> M) = ∅
-/
lemma mulIndicator_one (s : Set α) : (mulIndicator s fun _ => (1 : M)) = fun _ => (1 : M) :=
  mulIndicator_eq_one.2 <| by simp only [mulSupport_fun_one, empty_disjoint]

@[to_additive (attr := simp)]
/-
**Set.mulIndicator_one'** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_one' {s : Set α} : s.mulIndicator (1 : α -> M) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.mulIndicator_one`：mulIndicator_one (s : Set α) : (mulIndicator s fun
 _ => (1 : M)) = fun _ => (1 : M)
-/
lemma mulIndicator_one' {s : Set α} : s.mulIndicator (1 : α → M) = 1 :=
  mulIndicator_one M s

variable {M}

@[to_additive]
/-
**Set.mulIndicator_mulIndicator** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_mulIndicator (s t : Set α) (f : α -> M) : mulIndicator s (mul
Indicator t f) = mulIndicator (s inter t) f
参数：s t : Set α；f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
lemma mulIndicator_mulIndicator (s t : Set α) (f : α → M) :
    mulIndicator s (mulIndicator t f) = mulIndicator (s ∩ t) f :=
  funext fun x => by
    simp only [mulIndicator]
    split_ifs <;> simp_all +contextual

@[to_additive (attr := simp)]
/-
**Set.mulIndicator_inter_mulSupport** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_inter_mulSupport (s : Set α) (f : α -> M) : mulIndicator (s i
nter mulSupport f) f = mulIndicator s f
参数：s : Set α；f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.mulIndicator_mulIndicator`：mulIndicator_mulIndicator (s t : Set α) (
f : α -> M) : mulIndicator s (mulIndicator t f) = mulIndicator (s inter t) f
· 使用引理 `Set.mulIndicator_mulSupport`：mulIndicator_mulSupport : mulIndicator (mul
Support f) f = f
-/
lemma mulIndicator_inter_mulSupport (s : Set α) (f : α → M) :
    mulIndicator (s ∩ mulSupport f) f = mulIndicator s f := by
  rw [← mulIndicator_mulIndicator, mulIndicator_mulSupport]

@[to_additive]
/-
**Set.comp_mulIndicator** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：comp_mulIndicator (h : M -> β) (f : α -> M) {s : Set α} {x : α} [Decidable
Pred (· in s)] : h (s.mulIndicator f x) = s.piecewise (h ∘ f) (const α (h 1)) x
参数：h : M -> β；f : α -> M；· in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
· 使用定理 `Set.apply_piecewise`：apply_piecewise {δ' : α -> Sort*} (h : forall i, δ 
i -> δ' i) {x : α} : h x (s.piecewise f g x) = s.piecewise (fun x => h x (f x)) 
(fun x =>…
-/
lemma comp_mulIndicator (h : M → β) (f : α → M) {s : Set α} {x : α} [DecidablePred (· ∈ s)] :
    h (s.mulIndicator f x) = s.piecewise (h ∘ f) (const α (h 1)) x := by
  let := Classical.decPred (· ∈ s)
  convert! s.apply_piecewise f (const α 1) (fun _ => h) (x := x) using 2

@[to_additive]
/-
**Set.mulIndicator_comp_right** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_comp_right {s : Set α} (f : β -> α) {g : α -> M} {x : β} : mu
lIndicator (f ⁻¹' s) (g ∘ f) x = mulIndicator s g (f x)
参数：f : β -> α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mulIndicator_comp_right {s : Set α} (f : β → α) {g : α → M} {x : β} :
    mulIndicator (f ⁻¹' s) (g ∘ f) x = mulIndicator s g (f x) := by
  tauto

@[to_additive]
/-
**Set.mulIndicator_image** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_image {s : Set α} {f : β -> M} {g : α -> β} (hg : Injective g
) {x : α} : mulIndicator (g '' s) f (g x) = mulIndicator s (f ∘ g) x
参数：hg : Injective g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.mulIndicator_comp_right`：mulIndicator_comp_right {s : Set α} (f : β 
-> α) {g : α -> M} {x : β} : mulIndicator (f ⁻¹' s) (g ∘ f) x = mulIndicator s g
 (f x)
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
-/
lemma mulIndicator_image {s : Set α} {f : β → M} {g : α → β} (hg : Injective g) {x : α} :
    mulIndicator (g '' s) f (g x) = mulIndicator s (f ∘ g) x := by
  rw [← mulIndicator_comp_right, preimage_image_eq _ hg]

@[to_additive]
/-
**Set.mulIndicator_comp_of_one** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_comp_of_one {g : M -> N} (hg : g 1 = 1) : mulIndicator s (g ∘
 f) = g ∘ mulIndicator s f
参数：hg : g 1 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Set.mulIndicator_of_mem`：mulIndicator_of_mem (h : a in s) (f : α -> M) :
 mulIndicator s f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `Set.mulIndicator_of_notMem`：mulIndicator_of_notMem (h : a ∉ s) (f : α ->
 M) : mulIndicator s f a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma mulIndicator_comp_of_one {g : M → N} (hg : g 1 = 1) :
    mulIndicator s (g ∘ f) = g ∘ mulIndicator s f := by
  funext
  simp only [mulIndicator]
  split_ifs <;> simp [*]

@[to_additive]
/-
**Set.comp_mulIndicator_const** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：comp_mulIndicator_const (c : M) (f : M -> N) (hf : f 1 = 1) : (fun x => f 
(s.mulIndicator (fun _ => c) x)) = s.mulIndicator fun _ => f c
参数：c : M；f : M -> N；hf : f 1 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.mulIndicator_comp_of_one`：mulIndicator_comp_of_one {g : M -> N} (hg 
: g 1 = 1) : mulIndicator s (g ∘ f) = g ∘ mulIndicator s f
-/
lemma comp_mulIndicator_const (c : M) (f : M → N) (hf : f 1 = 1) :
    (fun x => f (s.mulIndicator (fun _ => c) x)) = s.mulIndicator fun _ => f c :=
  (mulIndicator_comp_of_one hf).symm

/-- Evaluating the indicator of a family of functions at a point commutes with the indicator:
`s.mulIndicator f a b = s.mulIndicator (f · b) a`. -/
@[to_additive]
/-
**Set.mulIndicator_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_apply_apply (f : α -> β -> M) (b : β) : s.mulIndicator f a b 
= s.mulIndicator (fun i => f i b) a
参数：f : α -> β -> M；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `Set.mulIndicator_of_mem`：mulIndicator_of_mem (h : a in s) (f : α -> M) :
 mulIndicator s f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Set.mulIndicator_of_notMem`：mulIndicator_of_notMem (h : a ∉ s) (f : α ->
 M) : mulIndicator s f a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
Evaluating the indicator of a family of functions at a point commutes with the i
ndicator:
`s.mulIndicator f a b = s.mulIndicator (f · b) a`.
-/
lemma mulIndicator_apply_apply (f : α → β → M) (b : β) :
    s.mulIndicator f a b = s.mulIndicator (fun i ↦ f i b) a := by
  by_cases h : a ∈ s <;> simp [h]

@[to_additive]
/-
**Set.mulIndicator_preimage** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_preimage (s : Set α) (f : α -> M) (B : Set M) : mulIndicator 
s f ⁻¹' B = s.ite (f ⁻¹' B) (1 ⁻¹' B)
参数：s : Set α；f : α -> M；B : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.piecewise_preimage`：piecewise_preimage (f g : α -> β) (t) : s.piecew
ise f g ⁻¹' t = s.ite (f ⁻¹' t) (g ⁻¹' t)
-/
lemma mulIndicator_preimage (s : Set α) (f : α → M) (B : Set M) :
    mulIndicator s f ⁻¹' B = s.ite (f ⁻¹' B) (1 ⁻¹' B) :=
  letI := Classical.decPred (· ∈ s)
  piecewise_preimage s f 1 B

@[to_additive]
/-
**Set.mulIndicator_one_preimage** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_one_preimage (s : Set M) : t.mulIndicator 1 ⁻¹' s in ({Set.un
iv, ∅} : Set (Set α))
参数：s : Set M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.mulIndicator_one'`：mulIndicator_one' {s : Set α} : s.mulIndicator (1
 : α -> M) = 1
· 使用引理 `Pi.one_def`：one_def : (1 : forall i, M i) = fun _ => 1
· 使用定理 `Set.preimage_const`：preimage_const (b : β) (s : Set β) [Decidable (b in 
s)] : (fun _ : α => b) ⁻¹' s = if b in s then univ else ∅
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma mulIndicator_one_preimage (s : Set M) :
    t.mulIndicator 1 ⁻¹' s ∈ ({Set.univ, ∅} : Set (Set α)) := by
  classical
  rw [mulIndicator_one', Pi.one_def, Set.preimage_const]
  split_ifs <;> simp

@[to_additive]
/-
**Set.mulIndicator_const_preimage_eq_union** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_const_preimage_eq_union (U : Set α) (s : Set M) (a : M) [Deci
dable (a in s)] [Decidable ((1 : M) in s)] : (U.mulIndicator fun _ => a) ⁻¹' s =
 (if a in s then U else ∅) union if (1 : M) in s then Uᶜ else ∅
参数：U : Set α；s : Set M；a : M；a in s；(1 : M) in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.mulIndicator_preimage`：mulIndicator_preimage (s : Set α) (f : α -> M
) (B : Set M) : mulIndicator s f ⁻¹' B = s.ite (f ⁻¹' B) (1 ⁻¹' B)
· 使用引理 `Pi.one_def`：one_def : (1 : forall i, M i) = fun _ => 1
· 使用定理 `Set.preimage_const`：preimage_const (b : β) (s : Set β) [Decidable (b in 
s)] : (fun _ : α => b) ⁻¹' s = if b in s then univ else ∅
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.ite_same`：ite_same (t s : Set α) : t.ite s s = s
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Set.ite_empty_right`：ite_empty_right (t s : Set α) : t.ite s ∅ = s inter
 t
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `Set.ite_empty_left`：ite_empty_left (t s : Set α) : t.ite ∅ s = s \ t
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用定理 `Set.union_self`：union_self (a : Set α) : a union a = a
-/
lemma mulIndicator_const_preimage_eq_union (U : Set α) (s : Set M) (a : M) [Decidable (a ∈ s)]
    [Decidable ((1 : M) ∈ s)] : (U.mulIndicator fun _ => a) ⁻¹' s =
      (if a ∈ s then U else ∅) ∪ if (1 : M) ∈ s then Uᶜ else ∅ := by
  rw [mulIndicator_preimage, Pi.one_def, Set.preimage_const, preimage_const]
  split_ifs <;> simp [← compl_eq_univ_sdiff]

@[to_additive]
/-
**Set.mulIndicator_const_preimage** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_const_preimage (U : Set α) (s : Set M) (a : M) : (U.mulIndica
tor fun _ => a) ⁻¹' s in ({Set.univ, U, Uᶜ, ∅} : Set (Set α))
参数：U : Set α；s : Set M；a : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.mulIndicator_const_preimage_eq_union`：mulIndicator_const_preimage_eq
_union (U : Set α) (s : Set M) (a : M) [Decidable (a in s)] [Decidable ((1 : M) 
in s)] : (U.mulIndicator fun _…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用定理 `Set.union_self`：union_self (a : Set α) : a union a = a
-/
lemma mulIndicator_const_preimage (U : Set α) (s : Set M) (a : M) :
    (U.mulIndicator fun _ => a) ⁻¹' s ∈ ({Set.univ, U, Uᶜ, ∅} : Set (Set α)) := by
  classical
    rw [mulIndicator_const_preimage_eq_union]
    split_ifs <;> simp

@[to_additive]
/-
**Set.mulIndicator_preimage_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_preimage_of_notMem (s : Set α) (f : α -> M) {t : Set M} (ht :
 (1 : M) ∉ t) : mulIndicator s f ⁻¹' t = f ⁻¹' t inter s
参数：s : Set α；f : α -> M；ht : (1 : M) ∉ t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.mulIndicator_preimage`：mulIndicator_preimage (s : Set α) (f : α -> M
) (B : Set M) : mulIndicator s f ⁻¹' B = s.ite (f ⁻¹' B) (1 ⁻¹' B)
· 使用定理 `Set.preimage_const_of_notMem`：preimage_const_of_notMem {b : β} {s : Set 
β} (h : b ∉ s) : (fun _ : α => b) ⁻¹' s = ∅
· 使用定理 `Set.ite_empty_right`：ite_empty_right (t s : Set α) : t.ite s ∅ = s inter
 t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulIndicator_preimage_of_notMem (s : Set α) (f : α → M) {t : Set M} (ht : (1 : M) ∉ t) :
    mulIndicator s f ⁻¹' t = f ⁻¹' t ∩ s := by
  simp [mulIndicator_preimage, Pi.one_def, Set.preimage_const_of_notMem ht]

@[to_additive]
/-
**Set.mem_range_mulIndicator** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mem_range_mulIndicator {r : M} {s : Set α} {f : α -> M} : r in range (mulI
ndicator s f) ↔ r = 1 ∧ s != univ ∨ r in f '' s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_range_mulIndicator {r : M} {s : Set α} {f : α → M} :
    r ∈ range (mulIndicator s f) ↔ r = 1 ∧ s ≠ univ ∨ r ∈ f '' s := by
  simp [mulIndicator, ite_eq_iff, exists_or, eq_univ_iff_forall, and_comm, or_comm,
    @eq_comm _ r 1]

@[to_additive]
/-
**Set.mulIndicator_rel_mulIndicator** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_rel_mulIndicator {r : M -> M -> Prop} (h1 : r 1 1) (ha : a in
 s -> r (f a) (g a)) : r (mulIndicator s f a) (mulIndicator s g a)
参数：h1 : r 1 1；ha : a in s -> r (f a) (g a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma mulIndicator_rel_mulIndicator {r : M → M → Prop} (h1 : r 1 1) (ha : a ∈ s → r (f a) (g a)) :
    r (mulIndicator s f a) (mulIndicator s g a) := by
  simp only [mulIndicator]
  split_ifs with has
  exacts [ha has, h1]
/-
**Set.indicator_one_preimage** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：indicator_one_preimage [Zero M] (U : Set α) (s : Set M) : U.indicator 1 ⁻¹
' s in ({Set.univ, U, Uᶜ, ∅} : Set (Set α))
参数：U : Set α；s : Set M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.indicator_const_preimage`：∀ {α : Type u_1} {M : Type u_3} [inst : Ze
ro M] (U : Set α) (s : Set M) (a : M),   (U.indicator fun x => a) ⁻¹' s ∈ {Set.u
niv, U, Uᶜ, ∅}
-/
lemma indicator_one_preimage [Zero M] (U : Set α) (s : Set M) :
    U.indicator 1 ⁻¹' s ∈ ({Set.univ, U, Uᶜ, ∅} : Set (Set α)) :=
  indicator_const_preimage _ _ 1

end Set

