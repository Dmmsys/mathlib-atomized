/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Notation.Indicator

/-!
# Indicator function

In this file, we prove basic results about the indicator of a set.

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

assert_not_exists MonoidWithZero

open Function

variable {α β γ M N : Type*}

namespace Set

section Monoid

variable [MulOneClass M] {s t : Set α} {a : α}

@[to_additive]
/-
**Set.mulIndicator_union_mul_inter_apply** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mulIndicator_union_mul_inter_apply (f : α -> M) (s t : Set α) (a : α) : mu
lIndicator (s union t) f a * mulIndicator (s inter t) f a = mulIndicator s f a *
 mulIndicator t f a
参数：f : α -> M；s t : Set α；a : α。
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
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用引理 `Set.mulIndicator_of_notMem`：mulIndicator_of_notMem (h : a ∉ s) (f : α ->
 M) : mulIndicator s f a = 1
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem mulIndicator_union_mul_inter_apply (f : α → M) (s t : Set α) (a : α) :
    mulIndicator (s ∪ t) f a * mulIndicator (s ∩ t) f a
      = mulIndicator s f a * mulIndicator t f a := by
  by_cases hs : a ∈ s <;> by_cases ht : a ∈ t <;> simp [*]

@[to_additive]
/-
**Set.mulIndicator_union_mul_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mulIndicator_union_mul_inter (f : α -> M) (s t : Set α) : mulIndicator (s 
union t) f * mulIndicator (s inter t) f = mulIndicator s f * mulIndicator t f
参数：f : α -> M；s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.mulIndicator_union_mul_inter_apply`：mulIndicator_union_mul_inter_app
ly (f : α -> M) (s t : Set α) (a : α) : mulIndicator (s union t) f a * mulIndica
tor (s inter t) f a = mulInd…
-/
theorem mulIndicator_union_mul_inter (f : α → M) (s t : Set α) :
    mulIndicator (s ∪ t) f * mulIndicator (s ∩ t) f = mulIndicator s f * mulIndicator t f :=
  funext <| mulIndicator_union_mul_inter_apply f s t

@[to_additive]
/-
**Set.mulIndicator_union_of_notMem_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mulIndicator_union_of_notMem_inter (h : a ∉ s inter t) (f : α -> M) : mulI
ndicator (s union t) f a = mulIndicator s f a * mulIndicator t f a
参数：h : a ∉ s inter t；f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mulIndicator_union_mul_inter_apply`：mulIndicator_union_mul_inter_app
ly (f : α -> M) (s t : Set α) (a : α) : mulIndicator (s union t) f a * mulIndica
tor (s inter t) f a = mulInd…
· 使用引理 `Set.mulIndicator_of_notMem`：mulIndicator_of_notMem (h : a ∉ s) (f : α ->
 M) : mulIndicator s f a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mulIndicator_union_of_notMem_inter (h : a ∉ s ∩ t) (f : α → M) :
    mulIndicator (s ∪ t) f a = mulIndicator s f a * mulIndicator t f a := by
  rw [← mulIndicator_union_mul_inter_apply f s t, mulIndicator_of_notMem h, mul_one]

@[to_additive]
/-
**Set.mulIndicator_union_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mulIndicator_union_of_disjoint (h : Disjoint s t) (f : α -> M) : mulIndica
tor (s union t) f = fun a => mulIndicator s f a * mulIndicator t f a
参数：h : Disjoint s t；f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.mulIndicator_union_of_notMem_inter`：mulIndicator_union_of_notMem_int
er (h : a ∉ s inter t) (f : α -> M) : mulIndicator (s union t) f a = mulIndicato
r s f a * mulIndicator t f a
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
-/
theorem mulIndicator_union_of_disjoint (h : Disjoint s t) (f : α → M) :
    mulIndicator (s ∪ t) f = fun a => mulIndicator s f a * mulIndicator t f a :=
  funext fun _ => mulIndicator_union_of_notMem_inter (fun ha => h.le_bot ha) _

open scoped symmDiff in
@[to_additive]
/-
**Set.mulIndicator_symmDiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mulIndicator_symmDiff (s t : Set α) (f : α -> M) : mulIndicator (s ∆ t) f 
= mulIndicator (s \ t) f * mulIndicator (t \ s) f
参数：s t : Set α；f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mulIndicator_union_of_disjoint`：mulIndicator_union_of_disjoint (h : 
Disjoint s t) (f : α -> M) : mulIndicator (s union t) f = fun a => mulIndicator 
s f a * mulIndicator t f…
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
· 使用定理 `disjoint_sdiff_self_right`：disjoint_sdiff_self_right : Disjoint x (y \ x
)
-/
theorem mulIndicator_symmDiff (s t : Set α) (f : α → M) :
    mulIndicator (s ∆ t) f = mulIndicator (s \ t) f * mulIndicator (t \ s) f :=
  mulIndicator_union_of_disjoint (disjoint_sdiff_self_right.mono_left sdiff_le) _

@[to_additive]
/-
**Set.mulIndicator_mul** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mulIndicator_mul (s : Set α) (f g : α -> M) : (mulIndicator s fun a => f a
 * g a) = fun a => mulIndicator s f a * mulIndicator s g a
参数：s : Set α；f g : α -> M。
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
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mulIndicator_mul (s : Set α) (f g : α → M) :
    (mulIndicator s fun a => f a * g a) = fun a => mulIndicator s f a * mulIndicator s g a := by
  funext
  simp only [mulIndicator]
  split_ifs
  · rfl
  rw [mul_one]

@[to_additive]
/-
**Set.mulIndicator_mul'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mulIndicator_mul' (s : Set α) (f g : α -> M) : mulIndicator s (f * g) = mu
lIndicator s f * mulIndicator s g
参数：s : Set α；f g : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mulIndicator_mul`：mulIndicator_mul (s : Set α) (f g : α -> M) : (mul
Indicator s fun a => f a * g a) = fun a => mulIndicator s f a * mulIndicator s g
 a
-/
theorem mulIndicator_mul' (s : Set α) (f g : α → M) :
    mulIndicator s (f * g) = mulIndicator s f * mulIndicator s g :=
  mulIndicator_mul s f g

@[to_additive (attr := simp)]
/-
**Set.mulIndicator_compl_mul_self_apply** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mulIndicator_compl_mul_self_apply (s : Set α) (f : α -> M) (a : α) : mulIn
dicator sᶜ f a * mulIndicator s f a = f a
参数：s : Set α；f : α -> M；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_cases`：by_cases {p q : Prop} (hpq : p -> q) (hnpq : ¬p -> q) : q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Set.mulIndicator_of_notMem`：mulIndicator_of_notMem (h : a ∉ s) (f : α ->
 M) : mulIndicator s f a = 1
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Set.mulIndicator_of_mem`：mulIndicator_of_mem (h : a in s) (f : α -> M) :
 mulIndicator s f a = f a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mulIndicator_compl_mul_self_apply (s : Set α) (f : α → M) (a : α) :
    mulIndicator sᶜ f a * mulIndicator s f a = f a :=
  by_cases (fun ha : a ∈ s => by simp [ha]) fun ha => by simp [ha]

@[to_additive (attr := simp)]
/-
**Set.mulIndicator_compl_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mulIndicator_compl_mul_self (s : Set α) (f : α -> M) : mulIndicator sᶜ f *
 mulIndicator s f = f
参数：s : Set α；f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.mulIndicator_compl_mul_self_apply`：mulIndicator_compl_mul_self_apply
 (s : Set α) (f : α -> M) (a : α) : mulIndicator sᶜ f a * mulIndicator s f a = f
 a
-/
theorem mulIndicator_compl_mul_self (s : Set α) (f : α → M) :
    mulIndicator sᶜ f * mulIndicator s f = f :=
  funext <| mulIndicator_compl_mul_self_apply s f

@[to_additive (attr := simp)]
/-
**Set.mulIndicator_self_mul_compl_apply** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mulIndicator_self_mul_compl_apply (s : Set α) (f : α -> M) (a : α) : mulIn
dicator s f a * mulIndicator sᶜ f a = f a
参数：s : Set α；f : α -> M；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_cases`：by_cases {p q : Prop} (hpq : p -> q) (hnpq : ¬p -> q) : q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Set.mulIndicator_of_mem`：mulIndicator_of_mem (h : a in s) (f : α -> M) :
 mulIndicator s f a = f a
· 使用引理 `Set.mulIndicator_of_notMem`：mulIndicator_of_notMem (h : a ∉ s) (f : α ->
 M) : mulIndicator s f a = 1
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem mulIndicator_self_mul_compl_apply (s : Set α) (f : α → M) (a : α) :
    mulIndicator s f a * mulIndicator sᶜ f a = f a :=
  by_cases (fun ha : a ∈ s => by simp [ha]) fun ha => by simp [ha]

@[to_additive (attr := simp)]
/-
**Set.mulIndicator_self_mul_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mulIndicator_self_mul_compl (s : Set α) (f : α -> M) : mulIndicator s f * 
mulIndicator sᶜ f = f
参数：s : Set α；f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.mulIndicator_self_mul_compl_apply`：mulIndicator_self_mul_compl_apply
 (s : Set α) (f : α -> M) (a : α) : mulIndicator s f a * mulIndicator sᶜ f a = f
 a
-/
theorem mulIndicator_self_mul_compl (s : Set α) (f : α → M) :
    mulIndicator s f * mulIndicator sᶜ f = f :=
  funext <| mulIndicator_self_mul_compl_apply s f

@[to_additive]
/-
**Set.mulIndicator_mul_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mulIndicator_mul_eq_left {f g : α -> M} (h : Disjoint (mulSupport f) (mulS
upport g)) : (mulSupport f).mulIndicator (f * g) = f
参数：h : Disjoint (mulSupport f) (mulSupport g)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Set.mulIndicator_congr`：mulIndicator_congr (h : EqOn f g s) : mulIndicat
or s f = mulIndicator s g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Function.notMem_mulSupport`：notMem_mulSupport : x ∉ mulSupport f ↔ f x =
 1
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.mul_apply`：mul_apply (f g : forall i, M i) (i : ι) : (f * g) i = f i 
* g i
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `Set.mulIndicator_mulSupport`：mulIndicator_mulSupport : mulIndicator (mul
Support f) f = f
-/
theorem mulIndicator_mul_eq_left {f g : α → M} (h : Disjoint (mulSupport f) (mulSupport g)) :
    (mulSupport f).mulIndicator (f * g) = f := by
  refine (mulIndicator_congr fun x hx => ?_).trans mulIndicator_mulSupport
  have : g x = 1 := notMem_mulSupport.1 (disjoint_left.1 h hx)
  rw [Pi.mul_apply, this, mul_one]

@[to_additive]
/-
**Set.mulIndicator_mul_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mulIndicator_mul_eq_right {f g : α -> M} (h : Disjoint (mulSupport f) (mul
Support g)) : (mulSupport g).mulIndicator (f * g) = g
参数：h : Disjoint (mulSupport f) (mulSupport g)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Set.mulIndicator_congr`：mulIndicator_congr (h : EqOn f g s) : mulIndicat
or s f = mulIndicator s g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Function.notMem_mulSupport`：notMem_mulSupport : x ∉ mulSupport f ↔ f x =
 1
· 使用定理 `Set.disjoint_right`：disjoint_right : Disjoint s t ↔ forall ⦃a⦄, a in t -
> a ∉ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.mul_apply`：mul_apply (f g : forall i, M i) (i : ι) : (f * g) i = f i 
* g i
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `Set.mulIndicator_mulSupport`：mulIndicator_mulSupport : mulIndicator (mul
Support f) f = f
-/
theorem mulIndicator_mul_eq_right {f g : α → M} (h : Disjoint (mulSupport f) (mulSupport g)) :
    (mulSupport g).mulIndicator (f * g) = g := by
  refine (mulIndicator_congr fun x hx => ?_).trans mulIndicator_mulSupport
  have : f x = 1 := notMem_mulSupport.1 (disjoint_right.1 h hx)
  rw [Pi.mul_apply, this, one_mul]

@[to_additive]
/-
**Set.mulIndicator_mul_compl_eq_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mulIndicator_mul_compl_eq_piecewise [DecidablePred (· in s)] (f g : α -> M
) : s.mulIndicator f * sᶜ.mulIndicator g = s.piecewise f g
参数：· in s；f g : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用引理 `Pi.mul_apply`：mul_apply (f g : forall i, M i) (i : ι) : (f * g) i = f i 
* g i
· 使用引理 `Set.mulIndicator_of_mem`：mulIndicator_of_mem (h : a in s) (f : α -> M) :
 mulIndicator s f a = f a
· 使用引理 `Set.mulIndicator_of_notMem`：mulIndicator_of_notMem (h : a ∉ s) (f : α ->
 M) : mulIndicator s f a = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.notMem_compl_iff`：notMem_compl_iff {x : α} : x ∉ sᶜ ↔ x in s
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `Set.mem_compl`：mem_compl {s : Set α} {x : α} (h : x ∉ s) : x in sᶜ
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem mulIndicator_mul_compl_eq_piecewise [DecidablePred (· ∈ s)] (f g : α → M) :
    s.mulIndicator f * sᶜ.mulIndicator g = s.piecewise f g := by
  ext x
  by_cases h : x ∈ s
  · rw [piecewise_eq_of_mem _ _ _ h, Pi.mul_apply, Set.mulIndicator_of_mem h,
      Set.mulIndicator_of_notMem (Set.notMem_compl_iff.2 h), mul_one]
  · rw [piecewise_eq_of_notMem _ _ _ h, Pi.mul_apply, Set.mulIndicator_of_notMem h,
      Set.mulIndicator_of_mem (Set.mem_compl h), one_mul]

/-- `Set.mulIndicator` as a `monoidHom`. -/
@[to_additive /-- `Set.indicator` as an `addMonoidHom`. -/]
/-
**Set.mulIndicatorHom** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：mulIndicatorHom {α} (M) [MulOneClass M] (s : Set α) : (α -> M) ->* α -> M 
where toFun
参数：M；s : Set α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mulIndicator_mul`：mulIndicator_mul (s : Set α) (f g : α -> M) : (mul
Indicator s fun a => f a * g a) = fun a => mulIndicator s f a * mulIndicator s g
 a

--- 原说明 ---
`Set.mulIndicator` as a `monoidHom`.
-/
noncomputable def mulIndicatorHom {α} (M) [MulOneClass M] (s : Set α) : (α → M) →* α → M where
  toFun := mulIndicator s
  map_one' := mulIndicator_one M s
  map_mul' := mulIndicator_mul s

end Monoid

section Group

variable {G : Type*} [Group G] {s t : Set α}

@[to_additive]
/-
**Set.mulIndicator_inv'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mulIndicator_inv' (s : Set α) (f : α -> G) : mulIndicator s f⁻¹ = (mulIndi
cator s f)⁻¹
参数：s : Set α；f : α -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_inv`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [ins
t_1 : DivisionMonoid β] (f : α →* β) (a : α), f a⁻¹ = (f a)⁻¹
-/
theorem mulIndicator_inv' (s : Set α) (f : α → G) : mulIndicator s f⁻¹ = (mulIndicator s f)⁻¹ :=
  (mulIndicatorHom G s).map_inv f

@[to_additive]
/-
**Set.mulIndicator_inv** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mulIndicator_inv (s : Set α) (f : α -> G) : (mulIndicator s fun a => (f a)
⁻¹) = fun a => (mulIndicator s f a)⁻¹
参数：s : Set α；f : α -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mulIndicator_inv'`：mulIndicator_inv' (s : Set α) (f : α -> G) : mulI
ndicator s f⁻¹ = (mulIndicator s f)⁻¹
-/
theorem mulIndicator_inv (s : Set α) (f : α → G) :
    (mulIndicator s fun a => (f a)⁻¹) = fun a => (mulIndicator s f a)⁻¹ :=
  mulIndicator_inv' s f

@[to_additive]
/-
**Set.mulIndicator_div** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mulIndicator_div (s : Set α) (f g : α -> G) : (mulIndicator s fun a => f a
 / g a) = fun a => mulIndicator s f a / mulIndicator s g a
参数：s : Set α；f g : α -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_div`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [ins
t_1 : DivisionMonoid β] (f : α →* β) (g h : α),   f (g / h) = f g / f h
-/
theorem mulIndicator_div (s : Set α) (f g : α → G) :
    (mulIndicator s fun a => f a / g a) = fun a => mulIndicator s f a / mulIndicator s g a :=
  (mulIndicatorHom G s).map_div f g

@[to_additive]
/-
**Set.mulIndicator_div'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mulIndicator_div' (s : Set α) (f g : α -> G) : mulIndicator s (f / g) = mu
lIndicator s f / mulIndicator s g
参数：s : Set α；f g : α -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mulIndicator_div`：mulIndicator_div (s : Set α) (f g : α -> G) : (mul
Indicator s fun a => f a / g a) = fun a => mulIndicator s f a / mulIndicator s g
 a
-/
theorem mulIndicator_div' (s : Set α) (f g : α → G) :
    mulIndicator s (f / g) = mulIndicator s f / mulIndicator s g :=
  mulIndicator_div s f g

@[to_additive indicator_compl']
/-
**Set.mulIndicator_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mulIndicator_compl (s : Set α) (f : α -> G) : mulIndicator sᶜ f = f * (mul
Indicator s f)⁻¹
参数：s : Set α；f : α -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_mul_inv_of_mul_eq`：eq_mul_inv_of_mul_eq (h : a * c = b) : a = b * c⁻¹
· 使用定理 `Set.mulIndicator_compl_mul_self`：mulIndicator_compl_mul_self (s : Set α)
 (f : α -> M) : mulIndicator sᶜ f * mulIndicator s f = f
-/
theorem mulIndicator_compl (s : Set α) (f : α → G) :
    mulIndicator sᶜ f = f * (mulIndicator s f)⁻¹ :=
  eq_mul_inv_of_mul_eq <| s.mulIndicator_compl_mul_self f

@[to_additive indicator_compl]
/-
**Set.mulIndicator_compl'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mulIndicator_compl' (s : Set α) (f : α -> G) : mulIndicator sᶜ f = f / mul
Indicator s f
参数：s : Set α；f : α -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.mulIndicator_compl`：mulIndicator_compl (s : Set α) (f : α -> G) : mu
lIndicator sᶜ f = f * (mulIndicator s f)⁻¹
-/
theorem mulIndicator_compl' (s : Set α) (f : α → G) :
    mulIndicator sᶜ f = f / mulIndicator s f := by rw [div_eq_mul_inv, mulIndicator_compl]

@[to_additive indicator_sdiff']
/-
**Set.mulIndicator_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mulIndicator_sdiff (h : s subseteq t) (f : α -> G) : mulIndicator (t \ s) 
f = mulIndicator t f * (mulIndicator s f)⁻¹
参数：h : s subseteq t；f : α -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_mul_inv_of_mul_eq`：eq_mul_inv_of_mul_eq (h : a * c = b) : a = b * c⁻¹
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.mul_def`：mul_def (f g : forall i, M i) : f * g = fun i => f i * g i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mulIndicator_union_of_disjoint`：mulIndicator_union_of_disjoint (h : 
Disjoint s t) (f : α -> M) : mulIndicator (s union t) f = fun a => mulIndicator 
s f a * mulIndicator t f…
· 使用定理 `disjoint_sdiff_self_left`：disjoint_sdiff_self_left : Disjoint (y \ x) x
· 使用定理 `Set.sdiff_union_self`：sdiff_union_self {s t : Set α} : s \ t union t = s
 union t
· 使用定理 `Set.union_eq_self_of_subset_right`：union_eq_self_of_subset_right {s t : 
Set α} (h : t subseteq s) : s union t = s
-/
theorem mulIndicator_sdiff (h : s ⊆ t) (f : α → G) :
    mulIndicator (t \ s) f = mulIndicator t f * (mulIndicator s f)⁻¹ :=
  eq_mul_inv_of_mul_eq <| by
    rw [Pi.mul_def, ← mulIndicator_union_of_disjoint, sdiff_union_self,
      union_eq_self_of_subset_right h]
    exact disjoint_sdiff_self_left

@[deprecated (since := "2026-06-03")] alias mulIndicator_diff := mulIndicator_sdiff

@[to_additive indicator_sdiff]
/-
**Set.mulIndicator_sdiff'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mulIndicator_sdiff' (h : s subseteq t) (f : α -> G) : mulIndicator (t \ s)
 f = mulIndicator t f / mulIndicator s f
参数：h : s subseteq t；f : α -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mulIndicator_sdiff`：mulIndicator_sdiff (h : s subseteq t) (f : α -> 
G) : mulIndicator (t \ s) f = mulIndicator t f * (mulIndicator s f)⁻¹
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
-/
theorem mulIndicator_sdiff' (h : s ⊆ t) (f : α → G) :
    mulIndicator (t \ s) f = mulIndicator t f / mulIndicator s f := by
  rw [mulIndicator_sdiff h, div_eq_mul_inv]

@[deprecated (since := "2026-06-03")] alias mulIndicator_diff' := mulIndicator_sdiff'

open scoped symmDiff in
@[to_additive]
/-
**Set.apply_mulIndicator_symmDiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：apply_mulIndicator_symmDiff {g : G -> β} (hg : forall x, g x⁻¹ = g x) (s t
 : Set α) (f : α -> G) (x : α) : g (mulIndicator (s ∆ t) f x) = g (mulIndicator 
s f x / mulIndicator t f x)
参数：hg : forall x, g x⁻¹ = g x；s t : Set α；f : α -> G；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.mulIndicator_of_notMem`：mulIndicator_of_notMem (h : a ∉ s) (f : α ->
 M) : mulIndicator s f a = 1
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Set.mulIndicator_of_mem`：mulIndicator_of_mem (h : a in s) (f : α -> M) :
 mulIndicator s f a = f a
· 使用定理 `div_self'`：div_self' (a : G) : a / a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem apply_mulIndicator_symmDiff {g : G → β} (hg : ∀ x, g x⁻¹ = g x)
    (s t : Set α) (f : α → G) (x : α) :
    g (mulIndicator (s ∆ t) f x) = g (mulIndicator s f x / mulIndicator t f x) := by
  by_cases hs : x ∈ s <;> by_cases ht : x ∈ t <;> simp [mem_symmDiff, *]

end Group

section One

@[to_additive]
/-
**Set.mulSupport_subset_subsingleton_of_disjoint_on_mulSupport** 是 Mathlib 中的一个引
理，位于命名空间 `Set`。
形式化陈述：mulSupport_subset_subsingleton_of_disjoint_on_mulSupport [One β] {s : γ ->
 Set α} (f : α -> β) (hs : Pairwise (Disjoint on (fun j => s j inter f.mulSuppor
t))) (i : α) (j : γ) (hj : i in s j) : (fun d => (s d).mulIndicator f i).mulSupp
ort subseteq {j}
参数：f : α -> β；hs : Pairwise (Disjoint on (fun j => s j inter f.mulSupport))；i : 
α；j : γ；hj : i in s j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Disjoint.eq_1`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : OrderB
ot α] (a b : α),   Disjoint a b = ∀ ⦃x : α⦄, x ≤ a → x ≤ b → x ≤ ⊥
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma mulSupport_subset_subsingleton_of_disjoint_on_mulSupport [One β] {s : γ → Set α} (f : α → β)
  (hs : Pairwise (Disjoint on (fun j ↦ s j ∩ f.mulSupport))) (i : α) (j : γ) (hj : i ∈ s j) :
    (fun d ↦ (s d).mulIndicator f i).mulSupport ⊆ {j} := by
  suffices ∀ j', j' ≠ j → {i} ⊆ s j → {i} ⊆ s j' → {i} ⊆ mulSupport f → False by by_contra; aesop
  intro j' h hj hj' hi
  simp only [Pairwise, Disjoint, Set.subset_inter_iff] at hs
  simpa using hs h ⟨hj', hi⟩ ⟨hj, hi⟩

end One

/-! ### Relationship with `Pi.mulSingle`/`Pi.single` -/

variable {ι : Type*} [DecidableEq ι] {M : Type*} [One M]

/-- On non-dependent functions, `Set.mulIndicator` on a singleton set equals `Pi.mulSingle`. -/
@[to_additive (attr := simp)
  /-- On non-dependent functions, `Set.indicator` on a singleton set equals `Pi.single`. -/]
/-
**Set.mulIndicator_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mulIndicator_singleton (i : ι) (f : ι -> M) : Set.mulIndicator {i} f = Pi.
mulSingle i (f i)
参数：i : ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Set.mulIndicator_apply`：mulIndicator_apply (s : Set α) (f : α -> M) (a :
 α) [Decidable (a in s)] : mulIndicator s f a = if a in s then f a else 1
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `Pi.mulSingle_apply`：mulSingle_apply (i : ι) (x : M) (i' : ι) : (mulSingl
e i x : ι -> M) i' = if i' = i then x else 1
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem mulIndicator_singleton (i : ι) (f : ι → M) :
    Set.mulIndicator {i} f = Pi.mulSingle i (f i) := by
  ext j
  simp only [Set.mulIndicator_apply, Pi.mulSingle_apply, Set.mem_singleton_iff]
  split_ifs with h <;> simp [h]

end Set

@[to_additive]
/-
**map_mulIndicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_mulIndicator {M N F : Type*} [One M] [One N] [FunLike F M N] [OneHomCl
ass F M N] (f : F) (s : Set α) (g : α -> M) (x : α) : f (s.mulIndicator g x) = s
.mulIndicator (f ∘ g) x
参数：f : F；s : Set α；g : α -> M；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `Set.mulIndicator_comp_of_one`：mulIndicator_comp_of_one {g : M -> N} (hg 
: g 1 = 1) : mulIndicator s (g ∘ f) = g ∘ mulIndicator s f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_mulIndicator {M N F : Type*} [One M] [One N] [FunLike F M N] [OneHomClass F M N] (f : F)
    (s : Set α) (g : α → M) (x : α) : f (s.mulIndicator g x) = s.mulIndicator (f ∘ g) x := by
  simp [Set.mulIndicator_comp_of_one]
