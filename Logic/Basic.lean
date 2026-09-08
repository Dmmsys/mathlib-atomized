/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Mathlib.Lean.Meta.Simp
public import Batteries.Logic
public import Batteries.Util.LibraryNote
public import Mathlib.Tactic.Attr.Register

/-!
# Basic logic properties

This file is one of the earliest imports in mathlib.

## Implementation notes

Theorems that require decidability hypotheses are in the namespace `Decidable`.
Classical versions are in the namespace `Classical`.
-/

@[expose] public section

open Function

section Miscellany

section CommSimproc

open Lean Meta Simp

/-
**eq_comm_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_comm_eq {α : Sort*} (a b : α) : (a = b) = (b = a)
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
theorem eq_comm_eq {α : Sort*} (a b : α) : (a = b) = (b = a) := by rw [@eq_comm _ a b]
/-
**iff_comm_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iff_comm_eq (a b : Prop) : (a ↔ b) = (b ↔ a)
参数：a b : Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_comm`：∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a)
-/
theorem iff_comm_eq (a b : Prop) : (a ↔ b) = (b ↔ a) := by rw [@iff_comm a b]

/-- On a goal of the form of `x = y`, also try to simplify `y = x`.

If simplifying `y = x` gives `y' = x'` then this simproc returns `x' = y'` (so that the use of
commutativity is transparent), otherwise it returns the result of simplifying `y = x` unmodified.
-/
simproc_decl eqComm (_ = _) := fun e => do
  let_expr Eq _ x y := e | return .continue
  let symmExpr ← mkEq y x
  let r ← withoutTheorems #[`eqComm,
    -- These theorems would cause an infinite loop:
    ``eq_comm, ``Bool.not_eq_eq_eq_not, `inv_eq_iff_eq_inv, `eq_inv_mul_iff_mul_eq,
    `eq_mul_inv_iff_mul_eq, `neg_eq_iff_eq_neg, `Function.Involutive.eq_iff,
    `vadd_eq_iff_eq_neg_vadd, `Equiv.eq_symm_apply,
    -- These theorems aren't commute-resistant (they turn an equality into a non-equality in a
    -- non-commutative way.)
    ``beq_iff_eq, ``funext_iff, ``eq_iff_iff, `Prod.swap_eq_iff_eq_swap, ``left_eq_dite_iff,
    ``right_eq_dite_iff] do
    withTraceNode `Meta.Tactic.simp (fun _ => return m!"commuting equality: {e}") <| simp symmExpr
  -- If no actual progress happened (modulo commutativity), return early.
  match_expr r.expr with
  | Eq _ y' x' =>
    if (y' == y && x' == x) || (y' == x && x' == y) then do
      return .continue none
  | _ => pure ()
  let symmR ← Result.mkEqTrans { expr := symmExpr, proof? := ← mkAppM ``eq_comm_eq #[x, y] } r
  -- If we started with `x = y`, and the result of simplifying `y = x` was `y' = x'`, then we want
  -- to end up with `x' = y'`.
  match_expr r.expr with
  | Eq _ y' x' =>
    return .visit (← symmR.mkEqTrans
      { expr := ← mkEq x' y', proof? := ← mkAppM ``eq_comm_eq #[y', x'] })
  | _ => return .done symmR

/-- On a goal of the form of `x ↔ y`, also try to simplify `y ↔ x`.

If simplifying `y ↔ x` gives `y' ↔ x'` then this simproc returns `x' ↔ y'` (so that the use of
commutativity is transparent), otherwise it returns the result of simplifying `y ↔ x` unmodified.
-/
simproc_decl iffComm (_ ↔ _) := fun e => do
  let_expr Iff x y := e | return .continue
  let symmExpr := .app (.app (.const ``Iff []) y) x
  let r ← withoutTheorems #[`iffComm,
      -- These theorems would cause an infinite loop:
      ``Iff.comm,
      -- These theorems aren't commute-resistant (they turn an iff into a non-iff in a
      -- non-commutative way).
      ``and_congr_left_iff, ``and_congr_right_iff,  ``iff_def, ``iff_def',
      ``iff_iff_implies_and_implies, ``Bool.coe_iff_coe] do
    withTraceNode `Meta.Tactic.simp (fun _ => return m!"commuting iff: {e}") <| simp symmExpr
  -- If no actual progress happened (modulo commutativity), return early.
  if r.expr == symmExpr || r.expr == e then return .continue
  let symmR ← Result.mkEqTrans { expr := symmExpr, proof? := ← mkAppM ``iff_comm_eq #[x, y] } r
  -- If we started with `x ↔ y`, and the result of simplifying `y ↔ x` was `y' ↔ x'`, then we want
  -- to end up with `x' ↔ y'`.
  match_expr r.expr with
  | Iff y' x' =>
    return .visit (← symmR.mkEqTrans
      { expr := .app (.app (.const ``Iff []) x') y', proof? := ← mkAppM ``iff_comm_eq #[y', x'] })
  | _ => return .done symmR

end CommSimproc

-- attribute [refl] HEq.refl -- FIXME This is still rejected after https://github.com/leanprover-community/mathlib4/pull/857

/-- An identity function with its main argument implicit. This will be printed as `hidden` even
if it is applied to a large term, so it can be used for elision,
as done in the `elide` and `unelide` tactics. -/
/-
**hidden** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：hidden {α : Sort*} {a : α}
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An identity function with its main argument implicit. This will be printed as `h
idden` even
if it is applied to a large term, so it can be used for elision,
as done in the `elide` and `unelide` tactics.
-/
abbrev hidden {α : Sort*} {a : α} := a

variable {α : Sort*}
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 10) decidableEq_of_subsingleton [Subsingleton α] : DecidableEq α :=
  fun a b ↦ isTrue (Subsingleton.elim a b)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton α] (p : α → Prop) : Subsingleton (Subtype p) :=
  ⟨fun ⟨x, _⟩ ⟨y, _⟩ ↦ by cases Subsingleton.elim x y; rfl⟩
/-
**congr_heq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：congr_heq {α β γ : Sort _} {f : α -> γ} {g : β -> γ} {x : α} {y : β} (h₁ :
 f ≍ g) (h₂ : x ≍ y) : f x = g y
参数：h₁ : f ≍ g；h₂ : x ≍ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem congr_heq {α β γ : Sort _} {f : α → γ} {g : β → γ} {x : α} {y : β}
    (h₁ : f ≍ g) (h₂ : x ≍ y) : f x = g y := by
  cases h₂; cases h₁; rfl
/-
**congr_arg_heq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Sort u_1} {β : α → Sort u_2} (f : (a : α) → β a) {a₁ a₂ : α}, a₁ = 
a₂ → f a₁ ≍ f a₂
参数：f : (a : α) → β a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congr_arg_heq {β : α → Sort*} (f : ∀ a, β a) :
    ∀ {a₁ a₂ : α}, a₁ = a₂ → f a₁ ≍ f a₂
  | _, _, rfl => HEq.rfl
/-
**dcongr_heq.** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dcongr_heq.{u, v}
    {α₁ α₂ : Sort u}
    {β₁ : α₁ → Sort v} {β₂ : α₂ → Sort v}
    {f₁ : ∀ a, β₁ a} {f₂ : ∀ a, β₂ a}
    {a₁ : α₁} {a₂ : α₂}
    (hargs : a₁ ≍ a₂)
    (ht : ∀ t₁ t₂, t₁ ≍ t₂ → β₁ t₁ = β₂ t₂)
    (hf : α₁ = α₂ → β₁ ≍ β₂ → f₁ ≍ f₂) :
    f₁ a₁ ≍ f₂ a₂ := by
  cases hargs
  cases funext fun v => ht v v .rfl
  cases hf rfl .rfl
  rfl
/-
**eq_iff_eq_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Sort u_1} {b c : α}, (∀ {a : α}, a = b ↔ a = c) ↔ b = c
参数：∀ {a : α}, a = b ↔ a = c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem eq_iff_eq_cancel_left {b c : α} : (∀ {a}, a = b ↔ a = c) ↔ b = c :=
  ⟨fun h ↦ by rw [← h], fun h a ↦ by rw [h]⟩
/-
**eq_iff_eq_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Sort u_1} {a b : α}, (∀ {c : α}, a = c ↔ b = c) ↔ a = b
参数：∀ {c : α}, a = c ↔ b = c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem eq_iff_eq_cancel_right {a b : α} : (∀ {c}, a = c ↔ b = c) ↔ a = b :=
  ⟨fun h ↦ by rw [h], fun h a ↦ by rw [h]⟩
/-
**ne_and_eq_iff_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ne_and_eq_iff_right {a b c : α} (h : b != c) : a != b ∧ a = c ↔ a = c
参数：h : b != c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_iff_right_of_imp`：∀ {b a : Prop}, (b → a) → (a ∧ b ↔ b)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ne_and_eq_iff_right {a b c : α} (h : b ≠ c) : a ≠ b ∧ a = c ↔ a = c :=
  and_iff_right_of_imp (fun h2 => h2.symm ▸ h.symm)

/-- Wrapper for adding elementary propositions to the type class systems.
Warning: this can easily be abused. See the rest of this docstring for details.

Certain propositions should not be treated as a class globally,
but sometimes it is very convenient to be able to use the type class system
in specific circumstances.

For example, `ZMod p` is a field if and only if `p` is a prime number.
In order to be able to find this field instance automatically by type class search,
we have to turn `p.Prime` into an instance implicit assumption.

On the other hand, making `Nat.Prime` a class would require a major refactoring of the library,
and it is questionable whether making `Nat.Prime` a class is desirable at all.
The compromise is to add the assumption `[Fact p.Prime]` to `ZMod.instField`.

In particular, this class is not intended for turning the type class system
into an automated theorem prover for first-order logic. -/
/-
**Fact** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Prop → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Wrapper for adding elementary propositions to the type class systems.
Warning: this can easily be abused. See the rest of this docstring for details.

Certain propositions should not be treated as a class globally,
but sometimes it is very convenient to be able to use the type class system
in specific circumstances.

For example, `ZMod p` is a field if and only if `p` is a prime number.
In order to be able to find this field instance automatically by type class sear
ch,
we have to turn `p.Prime` into an instance implicit assumption.

On the other hand, making `Nat.Prime` a class would require a major refactoring 
of the library,
and it is questionable whether making `Nat.Prime` a class is desirable at all.
The compromise is to add the assumption `[Fact p.Prime]` to `ZMod.instField`.

In particular, this class is not intended for turning the type class system
into an automated theorem prover for first-order logic.
-/
class Fact (p : Prop) : Prop where
  /-- `Fact.out` contains the unwrapped witness for the fact represented by the instance of
  `Fact p`. -/
  out : p

library_note «fact non-instances» /--
In most cases, we should not have global instances of `Fact`; typeclass search is not an
advanced proof search engine, and adding any such instance has the potential to cause
slowdowns everywhere. We instead declare them as lemmata and make them local instances as required.
-/
/-
**Fact.elim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fact.elim {p : Prop} (h : Fact p) : p
参数：h : Fact p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p

--- 原说明 ---
In most cases, we should not have global instances of `Fact`; typeclass search i
s not an
advanced proof search engine, and adding any such instance has the potential to 
cause
slowdowns everywhere. We instead declare them as lemmata and make them local ins
tances as required.
-/
theorem Fact.elim {p : Prop} (h : Fact p) : p := h.1
/-
**fact_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fact_iff {p : Prop} : Fact p ↔ p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
theorem fact_iff {p : Prop} : Fact p ↔ p := ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {p : Prop} [Decidable p] : Decidable (Fact p) :=
  decidable_of_iff _ fact_iff.symm

/-- Swaps two pairs of arguments to a function. -/
/-
**Function.swap** 是 Mathlib 中的一个缩写定义，位于命名空间 `Function`。
形式化陈述：swap {φ : α -> β -> Sort u₃} (f : forall x y, φ x y) : forall y x, φ x y
参数：f : forall x y, φ x y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Swaps two pairs of arguments to a function.
-/
abbrev Function.swap₂ {ι₁ ι₂ : Sort*} {κ₁ : ι₁ → Sort*} {κ₂ : ι₂ → Sort*}
    {φ : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → Sort*} (f : ∀ i₁ j₁ i₂ j₂, φ i₁ j₁ i₂ j₂)
    (i₂ j₂ i₁ j₁) : φ i₁ j₁ i₂ j₂ := f i₁ j₁ i₂ j₂

end Miscellany

/-!
### Declarations about propositional connectives
-/

section Propositional

/-! ### Declarations about `implies` -/

alias Iff.imp := imp_congr

@[deprecated (since := "2026-01-30")] alias imp_iff_right_iff := Classical.imp_iff_right_iff
@[deprecated (since := "2026-01-30")] alias and_or_imp := Classical.and_or_imp

/-- Provide modus tollens (`mt`) as dot notation for implications. -/
/-
**Function.mt** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {a b : Prop}, (a → b) → ¬b → ¬a
参数：a → b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a

--- 原说明 ---
Provide modus tollens (`mt`) as dot notation for implications.
-/
protected theorem Function.mt {a b : Prop} : (a → b) → ¬b → ¬a := mt

/-! ### Declarations about `not` -/

alias dec_em := Decidable.em

set_option linter.unusedDecidableInType false in
/-
**dec_em'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dec_em' (p : Prop) [Decidable p] : ¬p ∨ p
参数：p : Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `dec_em`：∀ (p : Prop) [Decidable p], p ∨ ¬p
-/
theorem dec_em' (p : Prop) [Decidable p] : ¬p ∨ p := (dec_em p).symm

alias em := Classical.em
/-
**em'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：em' (p : Prop) : ¬p ∨ p
参数：p : Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
-/
theorem em' (p : Prop) : ¬p ∨ p := (em p).symm
/-
**or_not** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：or_not {p : Prop} : p ∨ ¬p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
-/
theorem or_not {p : Prop} : p ∨ ¬p := em _
/-
**Decidable.eq_or_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Decidable.eq_or_ne {α : Sort*} (x y : α) [Decidable (x = y)] : x = y ∨ x !
= y
参数：x y : α；x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dec_em`：∀ (p : Prop) [Decidable p], p ∨ ¬p
-/
theorem Decidable.eq_or_ne {α : Sort*} (x y : α) [Decidable (x = y)] : x = y ∨ x ≠ y :=
  dec_em <| x = y
/-
**Decidable.ne_or_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Decidable.ne_or_eq {α : Sort*} (x y : α) [Decidable (x = y)] : x != y ∨ x 
= y
参数：x y : α；x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dec_em'`：dec_em' (p : Prop) [Decidable p] : ¬p ∨ p
-/
theorem Decidable.ne_or_eq {α : Sort*} (x y : α) [Decidable (x = y)] : x ≠ y ∨ x = y :=
  dec_em' <| x = y
/-
**eq_or_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
-/
theorem eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x ≠ y := em <| x = y
/-
**ne_or_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ne_or_eq {α : Sort*} (x y : α) : x != y ∨ x = y
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `em'`：em' (p : Prop) : ¬p ∨ p
-/
theorem ne_or_eq {α : Sort*} (x y : α) : x ≠ y ∨ x = y := em' <| x = y
/-
**by_contradiction** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：by_contradiction {p : Prop} : (¬p -> False) -> p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
-/
theorem by_contradiction {p : Prop} : (¬p → False) → p :=
  open scoped Classical in Decidable.byContradiction
/-
**by_cases** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：by_cases {p q : Prop} (hpq : p -> q) (hnpq : ¬p -> q) : q
参数：hpq : p -> q；hnpq : ¬p -> q。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem by_cases {p q : Prop} (hpq : p → q) (hnpq : ¬p → q) : q :=
  open scoped Classical in if hp : p then hpq hp else hnpq hp

alias by_contra := by_contradiction

library_note «decidable namespace» /--
In most of mathlib, we use the law of excluded middle (LEM) and the axiom of choice (AC) freely.
The `Decidable` namespace contains versions of lemmas from the root namespace that explicitly
attempt to avoid the axiom of choice, usually by adding decidability assumptions on the inputs.

You can check if a lemma uses the axiom of choice by using `#print axioms foo` and seeing if
`Classical.choice` appears in the list.
-/

library_note «decidable arguments» /--
As mathlib is primarily classical,
if the type signature of a `def` or `lemma` does not require any `Decidable` instances to state,
it is preferable not to introduce any `Decidable` instances that are needed in the proof
as arguments, but rather to use the `classical` tactic as needed.

In the other direction, when `Decidable` instances do appear in the type signature,
it is better to use explicitly introduced ones rather than allowing Lean to automatically infer
classical ones, as these may cause instance mismatch errors later.

Various types that (almost) never have provable decidability, such as `ℝ`, `Set α` or `Ideal R`,
are given global `DecidableEq` instances, so that no decidable arguments have to be provided.
-/

export Classical (not_not)

variable {a b : Prop}
/-
**of_not_not** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：of_not_not {a : Prop} : ¬¬a -> a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
-/
theorem of_not_not {a : Prop} : ¬¬a → a := by_contra
/-
**not_ne_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_ne_iff {α : Sort*} {a b : α} : ¬a != b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
-/
theorem not_ne_iff {α : Sort*} {a b : α} : ¬a ≠ b ↔ a = b := not_not
/-
**of_not_imp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：of_not_imp : ¬(a -> b) -> a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.of_not_imp`：∀ {a b : Prop} [Decidable a], ¬(a → b) → a
-/
theorem of_not_imp : ¬(a → b) → a := open scoped Classical in Decidable.of_not_imp

alias Not.decidable_imp_symm := Decidable.not_imp_symm
/-
**Not.imp_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Not.imp_symm : (¬a -> b) -> ¬b -> a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Not.decidable_imp_symm`：∀ {a b : Prop} [Decidable a], (¬a → b) → ¬b → a
-/
theorem Not.imp_symm : (¬a → b) → ¬b → a := open scoped Classical in Not.decidable_imp_symm
/-
**not_imp_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_imp_comm : ¬a -> b ↔ ¬b -> a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.not_imp_comm`：∀ {a b : Prop} [Decidable a] [Decidable b], ¬a →
 b ↔ ¬b → a
-/
theorem not_imp_comm : ¬a → b ↔ ¬b → a := open scoped Classical in Decidable.not_imp_comm
/-
**not_imp_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {a : Prop}, ¬a → a ↔ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.not_imp_self`：∀ {a : Prop} [Decidable a], ¬a → a ↔ a
-/
@[simp] theorem not_imp_self : ¬a → a ↔ a := open scoped Classical in Decidable.not_imp_self
/-
**Imp.swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Imp.swap {a b : Sort*} {c : Prop} : a -> b -> c ↔ b -> a -> c
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Imp.swap {a b : Sort*} {c : Prop} : a → b → c ↔ b → a → c :=
  ⟨fun h x y ↦ h y x, fun h x y ↦ h y x⟩

alias Iff.not := not_congr
/-
**Iff.not_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
参数：h : a ↔ ¬b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
-/
theorem Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b := h.not.trans not_not
/-
**Iff.not_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Iff.not_right (h : ¬a ↔ b) : a ↔ ¬b
参数：h : ¬a ↔ b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
-/
theorem Iff.not_right (h : ¬a ↔ b) : a ↔ ¬b := not_not.symm.trans h.not
/-
**Iff.ne** 是 Mathlib 中的一个定理，位于命名空间 `Iff`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c = d) → (a 
≠ b ↔ c ≠ d)
参数：a = b ↔ c = d；a ≠ b ↔ c ≠ d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
-/
protected lemma Iff.ne {α β : Sort*} {a b : α} {c d : β} : (a = b ↔ c = d) → (a ≠ b ↔ c ≠ d) :=
  Iff.not
/-
**Iff.ne_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Iff.ne_left {α β : Sort*} {a b : α} {c d : β} : (a = b ↔ c != d) -> (a != 
b ↔ c = d)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
-/
lemma Iff.ne_left {α β : Sort*} {a b : α} {c d : β} : (a = b ↔ c ≠ d) → (a ≠ b ↔ c = d) :=
  Iff.not_left
/-
**Iff.ne_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Iff.ne_right {α β : Sort*} {a b : α} {c d : β} : (a != b ↔ c = d) -> (a = 
b ↔ c != d)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_right`：Iff.not_right (h : ¬a ↔ b) : a ↔ ¬b
-/
lemma Iff.ne_right {α β : Sort*} {a b : α} {c d : β} : (a ≠ b ↔ c = d) → (a = b ↔ c ≠ d) :=
  Iff.not_right

/-! ### Declarations about `Xor` -/

/-- `Xor a b` is the exclusive-or of propositions. -/
/-
**Xor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Xor (a b : Prop)
参数：a b : Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Xor a b` is the exclusive-or of propositions.
-/
def Xor (a b : Prop) := (a ∧ ¬b) ∨ (b ∧ ¬a)

@[deprecated (since := "2026-04-27")] alias Xor' := Xor
/-
**xor_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {a b : Prop}, Xor a b ↔ a ∧ ¬b ∨ b ∧ ¬a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[grind =] theorem xor_def {a b : Prop} : Xor a b ↔ (a ∧ ¬b) ∨ (b ∧ ¬a) := Iff.rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Decidable a] [Decidable b] : Decidable (Xor a b) := inferInstanceAs (Decidable (Or ..))
/-
**xor_true** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Xor True = Not
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem xor_true : Xor True = Not := by grind
/-
**xor_false** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Xor False = id
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem xor_false : Xor False = id := by grind
/-
**xor_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：xor_comm (a b : Prop) : Xor a b = Xor b a
参数：a b : Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem xor_comm (a b : Prop) : Xor a b = Xor b a := by grind
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.Commutative Xor := ⟨xor_comm⟩
/-
**xor_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (a : Prop), Xor a a = False
参数：a : Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem xor_self (a : Prop) : Xor a a = False := by grind
/-
**xor_not_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {a b : Prop}, Xor (¬a) b ↔ (a ↔ b)
参数：¬a；a ↔ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem xor_not_left : Xor (¬a) b ↔ (a ↔ b) := by grind
/-
**xor_not_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {a b : Prop}, Xor a ¬b ↔ (a ↔ b)
参数：a ↔ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem xor_not_right : Xor a (¬b) ↔ (a ↔ b) := by grind
/-
**xor_not_not** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：xor_not_not : Xor (¬a) (¬b) ↔ Xor a b
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem xor_not_not : Xor (¬a) (¬b) ↔ Xor a b := by grind
/-
**Xor.or** 是 Mathlib 中的一个定理，位于命名空间 `Xor`。
形式化陈述：∀ {a b : Prop}, Xor a b → a ∨ b
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Xor.or (h : Xor a b) : a ∨ b := by grind

@[deprecated (since := "2026-04-27")]
protected alias Xor'.or := Xor.or

/-! ### Declarations about `and` -/

alias Iff.and := and_congr
alias ⟨And.rotate, _⟩ := and_rotate

/-
**and_symm_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：and_symm_right {α : Sort*} (a b : α) (p : Prop) : p ∧ a = b ↔ p ∧ b = a
参数：a b : α；p : Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem and_symm_right {α : Sort*} (a b : α) (p : Prop) : p ∧ a = b ↔ p ∧ b = a := by simp [eq_comm]
/-
**and_symm_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：and_symm_left {α : Sort*} (a b : α) (p : Prop) : a = b ∧ p ↔ b = a ∧ p
参数：a b : α；p : Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem and_symm_left {α : Sort*} (a b : α) (p : Prop) : a = b ∧ p ↔ b = a ∧ p := by simp [eq_comm]

/-! ### Declarations about `or` -/

alias Iff.or := or_congr
alias ⟨Or.rotate, _⟩ := or_rotate

/-
**Or.elim3** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Or.elim3 {c d : Prop} (h : a ∨ b ∨ c) (ha : a -> d) (hb : b -> d) (hc : c 
-> d) : d
参数：h : a ∨ b ∨ c；ha : a -> d；hb : b -> d；hc : c -> d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
-/
theorem Or.elim3 {c d : Prop} (h : a ∨ b ∨ c) (ha : a → d) (hb : b → d) (hc : c → d) : d :=
  Or.elim h ha fun h₂ ↦ Or.elim h₂ hb hc
/-
**Or.imp3** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Or.imp3 {d e c f : Prop} (had : a -> d) (hbe : b -> e) (hcf : c -> f) : a 
∨ b ∨ c -> d ∨ e ∨ f
参数：had : a -> d；hbe : b -> e；hcf : c -> f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
-/
theorem Or.imp3 {d e c f : Prop} (had : a → d) (hbe : b → e) (hcf : c → f) :
    a ∨ b ∨ c → d ∨ e ∨ f :=
  Or.imp had <| Or.imp hbe hcf

export Classical (or_iff_not_imp_left or_iff_not_imp_right)
/-
**not_or_of_imp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_or_of_imp : (a -> b) -> ¬a ∨ b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
-/
theorem not_or_of_imp : (a → b) → ¬a ∨ b := open scoped Classical in Decidable.not_or_of_imp

-- See Note [decidable namespace]
/-
**Decidable.or_not_of_imp** 是 Mathlib 中的一个定理，位于命名空间 `Decidable`。
形式化陈述：∀ {a b : Prop} [Decidable a], (a → b) → b ∨ ¬a
参数：a → b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Decidable.or_not_of_imp [Decidable a] (h : a → b) : b ∨ ¬a :=
  dite _ (Or.inl ∘ h) Or.inr
/-
**or_not_of_imp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：or_not_of_imp : (a -> b) -> b ∨ ¬a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.or_not_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → b ∨ ¬a
-/
theorem or_not_of_imp : (a → b) → b ∨ ¬a := open scoped Classical in Decidable.or_not_of_imp
/-
**imp_iff_not_or** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：imp_iff_not_or : a -> b ↔ ¬a ∨ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.imp_iff_not_or`：∀ {a b : Prop} [Decidable a], a → b ↔ ¬a ∨ b
-/
theorem imp_iff_not_or : a → b ↔ ¬a ∨ b := open scoped Classical in Decidable.imp_iff_not_or
/-
**imp_iff_or_not** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：imp_iff_or_not {b a : Prop} : b -> a ↔ a ∨ ¬b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.imp_iff_or_not`：∀ {b a : Prop} [Decidable b], b → a ↔ a ∨ ¬b
-/
theorem imp_iff_or_not {b a : Prop} : b → a ↔ a ∨ ¬b :=
  open scoped Classical in Decidable.imp_iff_or_not
/-
**not_imp_not** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_imp_not : ¬a -> ¬b ↔ b -> a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.not_imp_not`：∀ {a b : Prop} [Decidable a], ¬a → ¬b ↔ b → a
-/
theorem not_imp_not : ¬a → ¬b ↔ b → a := open scoped Classical in Decidable.not_imp_not

@[deprecated Classical.imp_and_neg_imp_iff (since := "2026-01-30")]
/-
**imp_and_neg_imp_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：imp_and_neg_imp_iff (p q : Prop) : (p -> q) ∧ (¬p -> q) ↔ q
参数：p q : Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.imp_and_neg_imp_iff`：∀ (p : Prop) {q : Prop}, (p → q) ∧ (¬p → 
q) ↔ q
-/
theorem imp_and_neg_imp_iff (p q : Prop) : (p → q) ∧ (¬p → q) ↔ q :=
  Classical.imp_and_neg_imp_iff p

/-- Provide the reverse of modus tollens (`mt`) as dot notation for implications. -/
/-
**Function.mtr** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {a b : Prop}, (¬a → ¬b) → b → a
参数：¬a → ¬b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a

--- 原说明 ---
Provide the reverse of modus tollens (`mt`) as dot notation for implications.
-/
protected theorem Function.mtr : (¬a → ¬b) → b → a := not_imp_not.mp
/-
**or_congr_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：or_congr_left' {c a b : Prop} (h : ¬c -> (a ↔ b)) : a ∨ c ↔ b ∨ c
参数：h : ¬c -> (a ↔ b)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.or_congr_left'`：∀ {c a b : Prop} [Decidable c], (¬c → (a ↔ b))
 → (a ∨ c ↔ b ∨ c)
-/
theorem or_congr_left' {c a b : Prop} (h : ¬c → (a ↔ b)) : a ∨ c ↔ b ∨ c :=
  open scoped Classical in Decidable.or_congr_left' h
/-
**or_congr_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：or_congr_right' {c : Prop} (h : ¬a -> (b ↔ c)) : a ∨ b ↔ a ∨ c
参数：h : ¬a -> (b ↔ c)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.or_congr_right'`：∀ {a b c : Prop} [Decidable a], (¬a → (b ↔ c)
) → (a ∨ b ↔ a ∨ c)
-/
theorem or_congr_right' {c : Prop} (h : ¬a → (b ↔ c)) : a ∨ b ↔ a ∨ c :=
  open scoped Classical in Decidable.or_congr_right' h

/-! ### Declarations about distributivity -/

/-! Declarations about `iff` -/

alias Iff.iff := iff_congr

-- @[simp] -- FIXME simp ignores proof rewrites
/-
**iff_mpr_iff_true_intro** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iff_mpr_iff_true_intro {P : Prop} (h : P) : Iff.mpr (iff_true_intro h) Tru
e.intro = h
参数：h : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iff_true_intro`：∀ {a : Prop}, a → (a ↔ True)
-/
theorem iff_mpr_iff_true_intro {P : Prop} (h : P) : Iff.mpr (iff_true_intro h) True.intro = h := rfl
/-
**imp_or** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：imp_or {a b c : Prop} : a -> b ∨ c ↔ (a -> b) ∨ (a -> c)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.imp_or`：∀ {a b c : Prop} [Decidable a], a → b ∨ c ↔ (a → b) ∨ 
(a → c)
-/
theorem imp_or {a b c : Prop} : a → b ∨ c ↔ (a → b) ∨ (a → c) :=
  open scoped Classical in Decidable.imp_or
/-
**imp_or'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：imp_or' {a : Sort*} {b c : Prop} : a -> b ∨ c ↔ (a -> b) ∨ (a -> c)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.imp_or'`：∀ {b : Prop} {a : Sort u_1} {c : Prop} [Decidable b],
 (∀ (a : a), b ∨ c) ↔ (∀ (a : a), b) ∨ ∀ (a : a), c
-/
theorem imp_or' {a : Sort*} {b c : Prop} : a → b ∨ c ↔ (a → b) ∨ (a → c) :=
  open scoped Classical in Decidable.imp_or'

@[deprecated (since := "2026-01-30")] alias not_imp := Classical.not_imp
/-
**peirce** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：peirce (a b : Prop) : ((a -> b) -> a) -> a
参数：a b : Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.peirce`：∀ (a b : Prop) [Decidable a], ((a → b) → a) → a
-/
theorem peirce (a b : Prop) : ((a → b) → a) → a := open scoped Classical in Decidable.peirce _ _
/-
**not_iff_not** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.not_iff_not`：∀ {a b : Prop} [Decidable a] [Decidable b], (¬a ↔
 ¬b) ↔ (a ↔ b)
-/
theorem not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b) := open scoped Classical in Decidable.not_iff_not
/-
**not_iff_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.not_iff_comm`：∀ {a b : Prop} [Decidable a] [Decidable b], (¬a 
↔ b) ↔ (¬b ↔ a)
-/
theorem not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a) := open scoped Classical in Decidable.not_iff_comm
/-
**not_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_iff : ¬(a ↔ b) ↔ (¬a ↔ b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.not_iff`：∀ {b a : Prop} [Decidable b], ¬(a ↔ b) ↔ (¬a ↔ b)
-/
theorem not_iff : ¬(a ↔ b) ↔ (¬a ↔ b) := open scoped Classical in Decidable.not_iff
/-
**iff_not_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iff_not_comm : (a ↔ ¬b) ↔ (b ↔ ¬a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.iff_not_comm`：∀ {a b : Prop} [Decidable a] [Decidable b], (a ↔
 ¬b) ↔ (b ↔ ¬a)
-/
theorem iff_not_comm : (a ↔ ¬b) ↔ (b ↔ ¬a) := open scoped Classical in Decidable.iff_not_comm
/-
**iff_iff_and_or_not_and_not** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iff_iff_and_or_not_and_not : (a ↔ b) ↔ a ∧ b ∨ ¬a ∧ ¬b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.iff_iff_and_or_not_and_not`：∀ {a b : Prop} [Decidable b], (a ↔
 b) ↔ a ∧ b ∨ ¬a ∧ ¬b
-/
theorem iff_iff_and_or_not_and_not : (a ↔ b) ↔ a ∧ b ∨ ¬a ∧ ¬b :=
  open scoped Classical in Decidable.iff_iff_and_or_not_and_not
/-
**iff_iff_not_or_and_or_not** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iff_iff_not_or_and_or_not : (a ↔ b) ↔ (¬a ∨ b) ∧ (a ∨ ¬b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.iff_iff_not_or_and_or_not`：∀ {a b : Prop} [Decidable a] [Decid
able b], (a ↔ b) ↔ (¬a ∨ b) ∧ (a ∨ ¬b)
-/
theorem iff_iff_not_or_and_or_not : (a ↔ b) ↔ (¬a ∨ b) ∧ (a ∨ ¬b) :=
  open scoped Classical in Decidable.iff_iff_not_or_and_or_not
/-
**not_and_not_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_and_not_right : ¬(a ∧ ¬b) ↔ a -> b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.not_and_not_right`：∀ {b a : Prop} [Decidable b], ¬(a ∧ ¬b) ↔ a
 → b
-/
theorem not_and_not_right : ¬(a ∧ ¬b) ↔ a → b :=
  open scoped Classical in Decidable.not_and_not_right

/-! ### De Morgan's laws -/

/-- One of **de Morgan's laws**: the negation of a conjunction is logically equivalent to the
disjunction of the negations. -/
/-
**not_and_or** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.not_and_iff_not_or_not`：∀ {a b : Prop} [Decidable a], ¬(a ∧ b)
 ↔ ¬a ∨ ¬b

--- 原说明 ---
One of **de Morgan's laws**: the negation of a conjunction is logically equivale
nt to the
disjunction of the negations.
-/
theorem not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b := open scoped Classical in Decidable.not_and_iff_not_or_not
/-
**or_iff_not_and_not** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：or_iff_not_and_not : a ∨ b ↔ ¬(¬a ∧ ¬b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.or_iff_not_not_and_not`：∀ {a b : Prop} [Decidable a] [Decidabl
e b], a ∨ b ↔ ¬(¬a ∧ ¬b)
-/
theorem or_iff_not_and_not : a ∨ b ↔ ¬(¬a ∧ ¬b) :=
  open scoped Classical in Decidable.or_iff_not_not_and_not
/-
**and_iff_not_or_not** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：and_iff_not_or_not : a ∧ b ↔ ¬(¬a ∨ ¬b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.and_iff_not_not_or_not`：∀ {a b : Prop} [Decidable a] [Decidabl
e b], a ∧ b ↔ ¬(¬a ∨ ¬b)
-/
theorem and_iff_not_or_not : a ∧ b ↔ ¬(¬a ∨ ¬b) :=
  open scoped Classical in Decidable.and_iff_not_not_or_not
/-
**not_xor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (P Q : Prop), ¬Xor P Q ↔ (P ↔ Q)
参数：P Q : Prop；P ↔ Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem not_xor (P Q : Prop) : ¬Xor P Q ↔ (P ↔ Q) := by
  simp only [not_and, Xor, not_or, not_not, ← iff_iff_implies_and_implies]
/-
**xor_iff_not_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：xor_iff_not_iff (P Q : Prop) : Xor P Q ↔ ¬(P ↔ Q)
参数：P Q : Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_right`：Iff.not_right (h : ¬a ↔ b) : a ↔ ¬b
· 使用定理 `not_xor`：∀ (P Q : Prop), ¬Xor P Q ↔ (P ↔ Q)
-/
theorem xor_iff_not_iff (P Q : Prop) : Xor P Q ↔ ¬(P ↔ Q) := (not_xor P Q).not_right
/-
**xor_iff_iff_not** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：xor_iff_iff_not : Xor a b ↔ (a ↔ ¬b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `xor_not_right`：∀ {a b : Prop}, Xor a ¬b ↔ (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem xor_iff_iff_not : Xor a b ↔ (a ↔ ¬b) := by simp only [← @xor_not_right a, not_not]
/-
**xor_iff_not_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：xor_iff_not_iff' : Xor a b ↔ (¬a ↔ b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `xor_not_left`：∀ {a b : Prop}, Xor (¬a) b ↔ (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem xor_iff_not_iff' : Xor a b ↔ (¬a ↔ b) := by simp only [← @xor_not_left _ b, not_not]
/-
**xor_iff_or_and_not_and** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：xor_iff_or_and_not_and (a b : Prop) : Xor a b ↔ (a ∨ b) ∧ (¬(a ∧ b))
参数：a b : Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Xor.eq_1`：∀ (a b : Prop), Xor a b = (a ∧ ¬b ∨ b ∧ ¬a)
· 使用定理 `or_and_right`：∀ {a b c : Prop}, (a ∨ b) ∧ c ↔ a ∧ c ∨ b ∧ c
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `and_or_left`：∀ {a b c : Prop}, a ∧ (b ∨ c) ↔ a ∧ b ∨ a ∧ c
· 使用定理 `and_not_self_iff`：∀ (a : Prop), a ∧ ¬a ↔ False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem xor_iff_or_and_not_and (a b : Prop) : Xor a b ↔ (a ∨ b) ∧ (¬(a ∧ b)) := by
  rw [Xor, or_and_right, not_and_or, and_or_left, and_not_self_iff, false_or,
    and_or_left, and_not_self_iff, or_false]

end Propositional

/-! ### Declarations about equality -/

section Equality

-- todo: change name
/-
**forall_cond_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_cond_comm {α} {s : α -> Prop} {p : α -> α -> Prop} : (forall a, s a
 -> forall b, s b -> p a b) ↔ forall a b, s a -> s b -> p a b
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall_cond_comm {α} {s : α → Prop} {p : α → α → Prop} :
    (∀ a, s a → ∀ b, s b → p a b) ↔ ∀ a b, s a → s b → p a b :=
  ⟨fun h a b ha hb ↦ h a ha b hb, fun h a ha b hb ↦ h a b ha hb⟩
/-
**forall_mem_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_mem_comm {α β} [Membership α β] {s : β} {p : α -> α -> Prop} : (for
all a (_ : a in s) b (_ : b in s), p a b) ↔ forall a b, a in s -> b in s -> p a 
b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_cond_comm`：forall_cond_comm {α} {s : α -> Prop} {p : α -> α -> Pr
op} : (forall a, s a -> forall b, s b -> p a b) ↔ forall a b, s a -> s b -> p a 
b
-/
theorem forall_mem_comm {α β} [Membership α β] {s : β} {p : α → α → Prop} :
    (∀ a (_ : a ∈ s) b (_ : b ∈ s), p a b) ↔ ∀ a b, a ∈ s → b ∈ s → p a b :=
  forall_cond_comm
/-
**ne_of_eq_of_ne** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ne_of_eq_of_ne {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ : b != c) : a != c
参数：h₁ : a = b；h₂ : b != c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ne_of_eq_of_ne {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ : b ≠ c) : a ≠ c := h₁.symm ▸ h₂
/-
**ne_of_ne_of_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ne_of_ne_of_eq {α : Sort*} {a b c : α} (h₁ : a != b) (h₂ : b = c) : a != c
参数：h₁ : a != b；h₂ : b = c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ne_of_ne_of_eq {α : Sort*} {a b c : α} (h₁ : a ≠ b) (h₂ : b = c) : a ≠ c := h₂ ▸ h₁

alias Eq.trans_ne := ne_of_eq_of_ne
alias Ne.trans_eq := ne_of_ne_of_eq
/-
**eq_equivalence** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_equivalence {α : Sort*} : Equivalence (@Eq α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem eq_equivalence {α : Sort*} : Equivalence (@Eq α) :=
  ⟨Eq.refl, @Eq.symm _, @Eq.trans _⟩

-- @[simp] -- FIXME simp ignores proof rewrites
/-
**congr_refl_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：congr_refl_left {α β : Sort*} (f : α -> β) {a b : α} (h : a = b) : congr (
Eq.refl f) h = congr_arg f h
参数：f : α -> β；h : a = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem congr_refl_left {α β : Sort*} (f : α → β) {a b : α} (h : a = b) :
    congr (Eq.refl f) h = congr_arg f h := rfl

-- @[simp] -- FIXME simp ignores proof rewrites
/-
**congr_refl_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：congr_refl_right {α β : Sort*} {f g : α -> β} (h : f = g) (a : α) : congr 
h (Eq.refl a) = congr_fun h a
参数：h : f = g；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem congr_refl_right {α β : Sort*} {f g : α → β} (h : f = g) (a : α) :
    congr h (Eq.refl a) = congr_fun h a := rfl

-- @[simp] -- FIXME simp ignores proof rewrites
/-
**congr_arg_refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：congr_arg_refl {α β : Sort*} (f : α -> β) (a : α) : congr_arg f (Eq.refl a
) = Eq.refl (f a)
参数：f : α -> β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem congr_arg_refl {α β : Sort*} (f : α → β) (a : α) :
    congr_arg f (Eq.refl a) = Eq.refl (f a) :=
  rfl

-- @[simp] -- FIXME simp ignores proof rewrites
/-
**congr_fun_rfl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：congr_fun_rfl {α β : Sort*} (f : α -> β) (a : α) : congr_fun (Eq.refl f) a
 = Eq.refl (f a)
参数：f : α -> β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem congr_fun_rfl {α β : Sort*} (f : α → β) (a : α) : congr_fun (Eq.refl f) a = Eq.refl (f a) :=
  rfl

-- @[simp] -- FIXME simp ignores proof rewrites
/-
**congr_fun_congr_arg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：congr_fun_congr_arg {α β γ : Sort*} (f : α -> β -> γ) {a a' : α} (p : a = 
a') (b : β) : congr_fun (congr_arg f p) b = congr_arg (fun a => f a b) p
参数：f : α -> β -> γ；p : a = a'；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem congr_fun_congr_arg {α β γ : Sort*} (f : α → β → γ) {a a' : α} (p : a = a') (b : β) :
    congr_fun (congr_arg f p) b = congr_arg (fun a ↦ f a b) p := rfl
/-
**rec_heq_of_heq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rec_heq_of_heq {α β : Sort _} {a b : α} {C : α -> Sort*} {x : C a} {y : β}
 (e : a = b) (h : x ≍ y) : e ▸ x ≍ y
参数：e : a = b；h : x ≍ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eqRec_heq_iff`：∀ {β : Sort v} {α : Sort u} {a : α} {motive : (b : α) → a
 = b → Sort v} {b : α} {refl : motive a ⋯} {h : a = b} {c : β},   h ▸ refl ≍ c ↔
 re…
-/
theorem rec_heq_of_heq {α β : Sort _} {a b : α} {C : α → Sort*} {x : C a} {y : β}
    (e : a = b) (h : x ≍ y) : e ▸ x ≍ y :=
  eqRec_heq_iff.mpr h

@[simp]
/-
**cast_heq_iff_heq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cast_heq_iff_heq {α β γ : Sort _} (e : α = β) (a : α) (c : γ) : cast e a ≍
 c ↔ a ≍ c
参数：e : α = β；a : α；c : γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cast_heq_iff_heq {α β γ : Sort _} (e : α = β) (a : α) (c : γ) :
    cast e a ≍ c ↔ a ≍ c := by subst e; rfl

@[simp]
/-
**heq_cast_iff_heq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：heq_cast_iff_heq {α β γ : Sort _} (e : β = γ) (a : α) (b : β) : a ≍ cast e
 b ↔ a ≍ b
参数：e : β = γ；a : α；b : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem heq_cast_iff_heq {α β γ : Sort _} (e : β = γ) (a : α) (b : β) :
    a ≍ cast e b ↔ a ≍ b := by subst e; rfl

universe u
variable {α β : Sort u} {e : β = α} {a : α} {b : β}
/-
**heq_of_eq_cast** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：heq_of_eq_cast (e : β = α) : a = cast e b -> a ≍ b
参数：e : β = α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma heq_of_eq_cast (e : β = α) : a = cast e b → a ≍ b := by rintro rfl; simp
/-
**eq_cast_iff_heq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_cast_iff_heq : a = cast e b ↔ a ≍ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `heq_of_eq_cast`：heq_of_eq_cast (e : β = α) : a = cast e b -> a ≍ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma eq_cast_iff_heq : a = cast e b ↔ a ≍ b := ⟨heq_of_eq_cast _, fun h ↦ by cases h; rfl⟩
/-
**heq_iff_exists_eq_cast** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：heq_iff_exists_eq_cast : a ≍ b ↔ exists (h : β = α), a = cast h b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `type_eq_of_heq`：∀ {α β : Sort u} {a : α} {b : β}, a ≍ b → α = β
· 使用定理 `HEq.symm`：∀ {α β : Sort u} {a : α} {b : β}, a ≍ b → b ≍ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `eq_cast_iff_heq`：eq_cast_iff_heq : a = cast e b ↔ a ≍ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cast_eq`：∀ {α : Sort u} (h : α = α) (a : α), cast h a = a
-/
lemma heq_iff_exists_eq_cast :
    a ≍ b ↔ ∃ (h : β = α), a = cast h b :=
  ⟨fun h ↦ ⟨type_eq_of_heq h.symm, eq_cast_iff_heq.mpr h⟩,
    by rintro ⟨rfl, h⟩; rw [h, cast_eq]⟩
/-
**heq_iff_exists_cast_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：heq_iff_exists_cast_eq : a ≍ b ↔ exists (h : α = β), cast h a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `heq_comm`：∀ {α β : Sort u_1} {a : α} {b : β}, a ≍ b ↔ b ≍ a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma heq_iff_exists_cast_eq :
    a ≍ b ↔ ∃ (h : α = β), cast h a = b := by
  simp only [heq_comm (a := a), heq_iff_exists_eq_cast, eq_comm]

end Equality

/-! ### Declarations about quantifiers -/
section Quantifiers
section Dependent

variable {α : Sort*} {β : α → Sort*} {γ : ∀ a, β a → Sort*}

/-
**forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall₂_imp {p q : ∀ a, β a → Prop} (h : ∀ a b, p a b → q a b) :
    (∀ a b, p a b) → ∀ a b, q a b :=
  forall_imp fun i ↦ forall_imp <| h i
/-
**forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall₃_imp {p q : ∀ a b, γ a b → Prop} (h : ∀ a b c, p a b c → q a b c) :
    (∀ a b c, p a b c) → ∀ a b c, q a b c :=
  forall_imp fun a ↦ forall₂_imp <| h a
/-
**Exists** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Sort u} → (α → Prop) → Prop
参数：α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Exists₂.imp {p q : ∀ a, β a → Prop} (h : ∀ a b, p a b → q a b) :
    (∃ a b, p a b) → ∃ a b, q a b :=
  Exists.imp fun a ↦ Exists.imp <| h a
/-
**Exists** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Sort u} → (α → Prop) → Prop
参数：α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Exists₃.imp {p q : ∀ a b, γ a b → Prop} (h : ∀ a b c, p a b c → q a b c) :
    (∃ a b c, p a b c) → ∃ a b c, q a b c :=
  Exists.imp fun a ↦ Exists₂.imp <| h a

end Dependent

variable {α β : Sort*} {p : α → Prop}

@[deprecated (since := "2026-03-25")] alias forall_swap := forall_comm

/-
**forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall₂_comm
    {ι₁ ι₂ : Sort*} {κ₁ : ι₁ → Sort*} {κ₂ : ι₂ → Sort*} {p : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → Prop} :
    (∀ i₁ j₁ i₂ j₂, p i₁ j₁ i₂ j₂) ↔ ∀ i₂ j₂ i₁ j₁, p i₁ j₁ i₂ j₂ := ⟨swap₂, swap₂⟩

@[deprecated (since := "2026-03-25")] alias forall₂_swap := forall₂_comm

/-- We intentionally restrict the type of `α` in this lemma so that this is a safer to use in simp
than `forall_comm`. -/
/-
**imp_forall_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：imp_forall_iff {α : Type*} {p : Prop} {q : α -> Prop} : (p -> forall x, q 
x) ↔ forall x, p -> q x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b

--- 原说明 ---
We intentionally restrict the type of `α` in this lemma so that this is a safer 
to use in simp
than `forall_comm`.
-/
theorem imp_forall_iff {α : Type*} {p : Prop} {q : α → Prop} : (p → ∀ x, q x) ↔ ∀ x, p → q x :=
  forall_comm
/-
**imp_forall_iff_forall** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：imp_forall_iff_forall (A : Prop) (B : A -> Prop) : (A -> forall h : A, B h
) ↔ forall h : A, B h
参数：A : Prop；B : A -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `forall_false`：∀ (p : False → Prop), (∀ (h : False), p h) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma imp_forall_iff_forall (A : Prop) (B : A → Prop) : (A → ∀ h : A, B h) ↔ ∀ h : A, B h := by
  by_cases h : A <;> simp [h]

@[deprecated (since := "2026-03-25")] alias exists_swap := exists_comm
/-
**exists_and_exists_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_and_exists_comm {P : α -> Prop} {Q : β -> Prop} : (exists a, P a) ∧
 (exists b, Q b) ↔ exists a b, P a ∧ Q b
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_and_exists_comm {P : α → Prop} {Q : β → Prop} :
    (∃ a, P a) ∧ (∃ b, Q b) ↔ ∃ a b, P a ∧ Q b :=
  ⟨fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ↦ ⟨a, b, ⟨ha, hb⟩⟩, fun ⟨a, b, ⟨ha, hb⟩⟩ ↦ ⟨⟨a, ha⟩, ⟨b, hb⟩⟩⟩

export Classical (not_forall)
/-
**not_forall_not** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_forall_not : (¬forall x, ¬p x) ↔ exists x, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.not_forall_not`：∀ {α : Sort u_1} {p : α → Prop} [Decidable (∃ 
x, p x)], (¬∀ (x : α), ¬p x) ↔ ∃ x, p x
-/
theorem not_forall_not : (¬∀ x, ¬p x) ↔ ∃ x, p x :=
  open scoped Classical in Decidable.not_forall_not

export Classical (not_exists_not)
/-
**forall_or_exists_not** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：forall_or_exists_not (P : α -> Prop) : (forall a, P a) ∨ exists a, ¬P a
参数：P : α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
-/
lemma forall_or_exists_not (P : α → Prop) : (∀ a, P a) ∨ ∃ a, ¬P a := by
  rw [← not_forall]; exact em _
/-
**exists_or_forall_not** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_or_forall_not (P : α -> Prop) : (exists a, P a) ∨ forall a, ¬P a
参数：P : α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
-/
lemma exists_or_forall_not (P : α → Prop) : (∃ a, P a) ∨ ∀ a, ¬P a := by
  rw [← not_exists]; exact em _
/-
**forall_imp_iff_exists_imp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_imp_iff_exists_imp {α : Sort*} {p : α -> Prop} {b : Prop} [ha : Non
empty α] : (forall x, p x) -> b ↔ exists x, p x -> b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_forall_not`：not_forall_not : (¬forall x, ¬p x) ↔ exists x, p x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.not_imp`：∀ {a b : Prop}, ¬(a → b) ↔ a ∧ ¬b
-/
theorem forall_imp_iff_exists_imp {α : Sort*} {p : α → Prop} {b : Prop} [ha : Nonempty α] :
    (∀ x, p x) → b ↔ ∃ x, p x → b := by
  classical
  let ⟨a⟩ := ha
  refine ⟨fun h ↦ not_forall_not.1 fun h' ↦ ?_, fun ⟨x, hx⟩ h ↦ hx (h x)⟩
  exact if hb : b then h' a fun _ ↦ hb else hb <| h fun x ↦ (Classical.not_imp.1 (h' x)).1

@[mfld_simps]
/-
**forall_true_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_true_iff : (α -> True) ↔ True
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `imp_true_iff`：∀ (α : Sort u), (∀ (a : α), True) ↔ True
-/
theorem forall_true_iff : (α → True) ↔ True := imp_true_iff _

-- Unfortunately this causes simp to loop sometimes, so we
-- add the 2 and 3 cases as simp lemmas instead
/-
**forall_true_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_true_iff' (h : forall a, p a ↔ True) : (forall a, p a) ↔ True
参数：h : forall a, p a ↔ True。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iff_true_intro`：∀ {a : Prop}, a → (a ↔ True)
· 使用定理 `of_iff_true`：∀ {a : Prop}, (a ↔ True) → a
-/
theorem forall_true_iff' (h : ∀ a, p a ↔ True) : (∀ a, p a) ↔ True :=
  iff_true_intro fun _ ↦ of_iff_true (h _)

-- This is not marked `@[simp]` because `implies_true : (α → True) = True` works
/-
**forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall₂_true_iff {β : α → Sort*} : (∀ a, β a → True) ↔ True := by simp

-- This is not marked `@[simp]` because `implies_true : (α → True) = True` works
/-
**forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall₃_true_iff {β : α → Sort*} {γ : ∀ a, β a → Sort*} :
    (∀ (a) (b : β a), γ a b → True) ↔ True := by simp
/-
**Decidable.and_forall_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Decidable.and_forall_ne [DecidableEq α] (a : α) {p : α -> Prop} : (p a ∧ f
orall b, b != a -> p b) ↔ forall b, p b
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_eq`：∀ {α : Sort u_1} {p : α → Prop} {a' : α}, (∀ (a : α), a = a' 
→ p a) ↔ p a'
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Decidable.and_forall_ne [DecidableEq α] (a : α) {p : α → Prop} :
    (p a ∧ ∀ b, b ≠ a → p b) ↔ ∀ b, p b := by
  simp only [← @forall_eq _ p a, ← forall_and, ← or_imp, Decidable.em, forall_const]
/-
**and_forall_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：and_forall_ne (a : α) : (p a ∧ forall b, b != a -> p b) ↔ forall b, p b
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.and_forall_ne`：Decidable.and_forall_ne [DecidableEq α] (a : α)
 {p : α -> Prop} : (p a ∧ forall b, b != a -> p b) ↔ forall b, p b
-/
theorem and_forall_ne (a : α) : (p a ∧ ∀ b, b ≠ a → p b) ↔ ∀ b, p b :=
  open scoped Classical in Decidable.and_forall_ne a
/-
**Ne.ne_or_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ne.ne_or_ne {x y : α} (z : α) (h : x != y) : x != z ∨ y != z
参数：z : α；h : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `and_imp`：∀ {a b c : Prop}, a ∧ b → c ↔ a → b → c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem Ne.ne_or_ne {x y : α} (z : α) (h : x ≠ y) : x ≠ z ∨ y ≠ z :=
  not_and_or.1 <| mt (and_imp.2 (· ▸ ·)) h.symm

@[simp]
/-
**exists_apply_eq_apply'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_apply_eq_apply' (f : α -> β) (a' : α) : exists a, f a' = f a
参数：f : α -> β；a' : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_apply_eq_apply' (f : α → β) (a' : α) : ∃ a, f a' = f a := ⟨a', rfl⟩

@[simp]
/-
**exists_apply_eq_apply2** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_apply_eq_apply2 {α β γ} {f : α -> β -> γ} {a : α} {b : β} : exists 
x y, f x y = f a b
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists_apply_eq_apply2 {α β γ} {f : α → β → γ} {a : α} {b : β} : ∃ x y, f x y = f a b :=
  ⟨a, b, rfl⟩

@[simp]
/-
**exists_apply_eq_apply2'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_apply_eq_apply2' {α β γ} {f : α -> β -> γ} {a : α} {b : β} : exists
 x y, f a b = f x y
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists_apply_eq_apply2' {α β γ} {f : α → β → γ} {a : α} {b : β} : ∃ x y, f a b = f x y :=
  ⟨a, b, rfl⟩

@[simp]
/-
**exists_apply_eq_apply3** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_apply_eq_apply3 {α β γ δ} {f : α -> β -> γ -> δ} {a : α} {b : β} {c
 : γ} : exists x y z, f x y z = f a b c
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists_apply_eq_apply3 {α β γ δ} {f : α → β → γ → δ} {a : α} {b : β} {c : γ} :
    ∃ x y z, f x y z = f a b c :=
  ⟨a, b, c, rfl⟩

@[simp]
/-
**exists_apply_eq_apply3'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_apply_eq_apply3' {α β γ δ} {f : α -> β -> γ -> δ} {a : α} {b : β} {
c : γ} : exists x y z, f a b c = f x y z
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists_apply_eq_apply3' {α β γ δ} {f : α → β → γ → δ} {a : α} {b : β} {c : γ} :
    ∃ x y z, f a b c = f x y z :=
  ⟨a, b, c, rfl⟩

/--
The constant function witnesses that
there exists a function sending a given term to a given term.

This is sometimes useful in `simp` to discharge side conditions.
-/
/-
**exists_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_apply_eq (a : α) (b : β) : exists f : α -> β, f a = b
参数：a : α；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant function witnesses that
there exists a function sending a given term to a given term.

This is sometimes useful in `simp` to discharge side conditions.
-/
theorem exists_apply_eq (a : α) (b : β) : ∃ f : α → β, f a = b := ⟨fun _ ↦ b, rfl⟩
/-
**exists_exists_and_eq_and** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β} {p : α → Prop} {q : β → Prop},
   (∃ b, (∃ a, p a ∧ f a = b) ∧ q b) ↔ ∃ a, p a ∧ q (f a)
参数：∃ b, (∃ a, p a ∧ f a = b) ∧ q b；f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] theorem exists_exists_and_eq_and {f : α → β} {p : α → Prop} {q : β → Prop} :
    (∃ b, (∃ a, p a ∧ f a = b) ∧ q b) ↔ ∃ a, p a ∧ q (f a) :=
  ⟨fun ⟨_, ⟨a, ha, hab⟩, hb⟩ ↦ ⟨a, ha, hab.symm ▸ hb⟩, fun ⟨a, hp, hq⟩ ↦ ⟨f a, ⟨a, hp, rfl⟩, hq⟩⟩
/-
**exists_exists_eq_and** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β} {p : β → Prop}, (∃ b, (∃ a, f 
a = b) ∧ p b) ↔ ∃ a, p (f a)
参数：∃ b, (∃ a, f a = b) ∧ p b；f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] theorem exists_exists_eq_and {f : α → β} {p : β → Prop} :
    (∃ b, (∃ a, f a = b) ∧ p b) ↔ ∃ a, p (f a) :=
  ⟨fun ⟨_, ⟨a, ha⟩, hb⟩ ↦ ⟨a, ha.symm ▸ hb⟩, fun ⟨a, ha⟩ ↦ ⟨f a, ⟨a, rfl⟩, ha⟩⟩
/-
**exists_exists_and_exists_and_eq_and** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} {f : α → β → γ} {p : α → Pr
op} {q : β → Prop} {r : γ → Prop},   (∃ c, (∃ a, p a ∧ ∃ b, q b ∧ f a b = c) ∧ r
 c) ↔ ∃ a, p a ∧ ∃ b, q b ∧ r (f a b)
参数：∃ c, (∃ a, p a ∧ ∃ b, q b ∧ f a b = c) ∧ r c；f a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] theorem exists_exists_and_exists_and_eq_and {α β γ : Type*}
    {f : α → β → γ} {p : α → Prop} {q : β → Prop} {r : γ → Prop} :
    (∃ c, (∃ a, p a ∧ ∃ b, q b ∧ f a b = c) ∧ r c) ↔ ∃ a, p a ∧ ∃ b, q b ∧ r (f a b) :=
  ⟨fun ⟨_, ⟨a, ha, b, hb, hab⟩, hc⟩ ↦ ⟨a, ha, b, hb, hab.symm ▸ hc⟩,
    fun ⟨a, ha, b, hb, hab⟩ ↦ ⟨f a b, ⟨a, ha, b, hb, rfl⟩, hab⟩⟩
/-
**exists_exists_exists_and_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} {f : α → β → γ} {p : γ → Pr
op},   (∃ c, (∃ a b, f a b = c) ∧ p c) ↔ ∃ a b, p (f a b)
参数：∃ c, (∃ a b, f a b = c) ∧ p c；f a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] theorem exists_exists_exists_and_eq {α β γ : Type*}
    {f : α → β → γ} {p : γ → Prop} :
    (∃ c, (∃ a, ∃ b, f a b = c) ∧ p c) ↔ ∃ a, ∃ b, p (f a b) :=
  ⟨fun ⟨_, ⟨a, b, hab⟩, hc⟩ ↦ ⟨a, b, hab.symm ▸ hc⟩,
    fun ⟨a, b, hab⟩ ↦ ⟨f a b, ⟨a, b, rfl⟩, hab⟩⟩
/-
**forall_apply_eq_imp_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_apply_eq_imp_iff' {f : α -> β} {p : β -> Prop} : (forall a b, f a =
 b -> p b) ↔ forall a, p (f a)
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem forall_apply_eq_imp_iff' {f : α → β} {p : β → Prop} :
    (∀ a b, f a = b → p b) ↔ ∀ a, p (f a) := by simp
/-
**forall_eq_apply_imp_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_eq_apply_imp_iff' {f : α -> β} {p : β -> Prop} : (forall a b, b = f
 a -> p b) ↔ forall a, p (f a)
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem forall_eq_apply_imp_iff' {f : α → β} {p : β → Prop} :
    (∀ a b, b = f a → p b) ↔ ∀ a, p (f a) := by simp
/-
**exists** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists₂_comm
    {ι₁ ι₂ : Sort*} {κ₁ : ι₁ → Sort*} {κ₂ : ι₂ → Sort*} {p : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → Prop} :
    (∃ i₁ j₁ i₂ j₂, p i₁ j₁ i₂ j₂) ↔ ∃ i₂ j₂ i₁ j₁, p i₁ j₁ i₂ j₂ := by
  simp only [@exists_comm (κ₁ _), @exists_comm ι₁]
/-
**And.exists** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：And.exists {p q : Prop} {f : p ∧ q -> Prop} : (exists h, f h) ↔ exists hp 
hq, f ⟨hp, hq⟩
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem And.exists {p q : Prop} {f : p ∧ q → Prop} : (∃ h, f h) ↔ ∃ hp hq, f ⟨hp, hq⟩ :=
  ⟨fun ⟨h, H⟩ ↦ ⟨h.1, h.2, H⟩, fun ⟨hp, hq, H⟩ ↦ ⟨⟨hp, hq⟩, H⟩⟩
/-
**forall_or_of_or_forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_or_of_or_forall {α : Sort*} {p : α -> Prop} {b : Prop} (h : b ∨ for
all x, p x) (x : α) : b ∨ p x
参数：h : b ∨ forall x, p x；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
-/
theorem forall_or_of_or_forall {α : Sort*} {p : α → Prop} {b : Prop} (h : b ∨ ∀ x, p x) (x : α) :
    b ∨ p x :=
  h.imp_right fun h₂ ↦ h₂ x

-- See Note [decidable namespace]
/-
**Decidable.forall_or_left** 是 Mathlib 中的一个定理，位于命名空间 `Decidable`。
形式化陈述：∀ {α : Sort u_1} {q : Prop} {p : α → Prop} [Decidable q], (∀ (x : α), q ∨ 
p x) ↔ q ∨ ∀ (x : α), p x
参数：∀ (x : α), q ∨ p x；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `forall_or_of_or_forall`：forall_or_of_or_forall {α : Sort*} {p : α -> Pro
p} {b : Prop} (h : b ∨ forall x, p x) (x : α) : b ∨ p x
-/
protected theorem Decidable.forall_or_left {q : Prop} {p : α → Prop} [Decidable q] :
    (∀ x, q ∨ p x) ↔ q ∨ ∀ x, p x :=
  ⟨fun h ↦ if hq : q then Or.inl hq else
    Or.inr fun x ↦ (h x).resolve_left hq, forall_or_of_or_forall⟩
/-
**forall_or_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_or_left {q} {p : α -> Prop} : (forall x, q ∨ p x) ↔ q ∨ forall x, p
 x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.forall_or_left`：∀ {α : Sort u_1} {q : Prop} {p : α → Prop} [De
cidable q], (∀ (x : α), q ∨ p x) ↔ q ∨ ∀ (x : α), p x
-/
theorem forall_or_left {q} {p : α → Prop} : (∀ x, q ∨ p x) ↔ q ∨ ∀ x, p x :=
  open scoped Classical in Decidable.forall_or_left

-- See Note [decidable namespace]
/-
**Decidable.forall_or_right** 是 Mathlib 中的一个定理，位于命名空间 `Decidable`。
形式化陈述：∀ {α : Sort u_1} {q : Prop} {p : α → Prop} [Decidable q], (∀ (x : α), p x 
∨ q) ↔ (∀ (x : α), p x) ∨ q
参数：∀ (x : α), p x ∨ q；∀ (x : α), p x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem Decidable.forall_or_right {q} {p : α → Prop} [Decidable q] :
    (∀ x, p x ∨ q) ↔ (∀ x, p x) ∨ q := by simp [or_comm, Decidable.forall_or_left]
/-
**forall_or_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_or_right {q} {p : α -> Prop} : (forall x, p x ∨ q) ↔ (forall x, p x
) ∨ q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.forall_or_right`：∀ {α : Sort u_1} {q : Prop} {p : α → Prop} [D
ecidable q], (∀ (x : α), p x ∨ q) ↔ (∀ (x : α), p x) ∨ q
-/
theorem forall_or_right {q} {p : α → Prop} : (∀ x, p x ∨ q) ↔ (∀ x, p x) ∨ q :=
  open scoped Classical in Decidable.forall_or_right

@[simp]
/-
**forall_and_index** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_and_index {p q : Prop} {r : p ∧ q -> Prop} : (forall h : p ∧ q, r h
) ↔ forall (hp : p) (hq : q), r ⟨hp, hq⟩
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem forall_and_index {p q : Prop} {r : p ∧ q → Prop} :
    (∀ h : p ∧ q, r h) ↔ ∀ (hp : p) (hq : q), r ⟨hp, hq⟩ :=
  ⟨fun h hp hq ↦ h ⟨hp, hq⟩, fun h h1 ↦ h h1.1 h1.2⟩
/-
**forall_and_index'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_and_index' {p q : Prop} {r : p -> q -> Prop} : (forall (hp : p) (hq
 : q), r hp hq) ↔ forall h : p ∧ q, r h.1 h.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `forall_and_index`：forall_and_index {p q : Prop} {r : p ∧ q -> Prop} : (f
orall h : p ∧ q, r h) ↔ forall (hp : p) (hq : q), r ⟨hp, hq⟩
-/
theorem forall_and_index' {p q : Prop} {r : p → q → Prop} :
    (∀ (hp : p) (hq : q), r hp hq) ↔ ∀ h : p ∧ q, r h.1 h.2 :=
  (forall_and_index (r := fun h => r h.1 h.2)).symm
/-
**Exists.fst** 是 Mathlib 中的一个定理，位于命名空间 `Exists`。
形式化陈述：∀ {b : Prop} {p : b → Prop}, Exists p → b
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Exists.fst {b : Prop} {p : b → Prop} : Exists p → b
  | ⟨h, _⟩ => h
/-
**Exists.snd** 是 Mathlib 中的一个定理，位于命名空间 `Exists`。
形式化陈述：∀ {b : Prop} {p : b → Prop} (h : Exists p), p ⋯
参数：h : Exists p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.fst`：∀ {b : Prop} {p : b → Prop}, Exists p → b
-/
theorem Exists.snd {b : Prop} {p : b → Prop} : ∀ h : Exists p, p h.fst
  | ⟨_, h⟩ => h
/-
**Prop.exists_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prop.exists_iff {p : Prop -> Prop} : (exists h, p h) ↔ p False ∨ p True
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_cases`：by_cases {p q : Prop} (hpq : p -> q) (hnpq : ¬p -> q) : q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
-/
theorem Prop.exists_iff {p : Prop → Prop} : (∃ h, p h) ↔ p False ∨ p True :=
  ⟨fun ⟨h₁, h₂⟩ ↦ by_cases (fun H : h₁ ↦ .inr <| by simpa only [H] using h₂)
    (fun H ↦ .inl <| by simpa only [H] using h₂), fun h ↦ h.elim (.intro _) (.intro _)⟩
/-
**Prop.forall_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prop.forall_iff {p : Prop -> Prop} : (forall h, p h) ↔ p False ∧ p True
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem Prop.forall_iff {p : Prop → Prop} : (∀ h, p h) ↔ p False ∧ p True :=
  ⟨fun H ↦ ⟨H _, H _⟩, fun ⟨h₁, h₂⟩ h ↦ by by_cases H : h <;> simpa only [H]⟩
/-
**exists_iff_of_forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_iff_of_forall {p : Prop} {q : p -> Prop} (h : forall h, q h) : (exi
sts h, q h) ↔ p
参数：h : forall h, q h。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.fst`：∀ {b : Prop} {p : b → Prop}, Exists p → b
-/
theorem exists_iff_of_forall {p : Prop} {q : p → Prop} (h : ∀ h, q h) : (∃ h, q h) ↔ p :=
  ⟨Exists.fst, fun H ↦ ⟨H, h H⟩⟩
/-
**exists_prop_of_false** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_prop_of_false {p : Prop} {q : p -> Prop} : ¬p -> ¬exists h' : p, q 
h'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Exists.fst`：∀ {b : Prop} {p : b → Prop}, Exists p → b
-/
theorem exists_prop_of_false {p : Prop} {q : p → Prop} : ¬p → ¬∃ h' : p, q h' :=
  mt Exists.fst

/-! See `IsEmpty.exists_iff` for the `False` version of `exists_true_left`. -/

/-
**forall_prop_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_prop_congr {p p' : Prop} {q q' : p -> Prop} (hq : forall h, q h ↔ q
' h) (hp : p ↔ p') : (forall h, q h) ↔ forall h : p', q' (hp.2 h)
参数：hq : forall h, q h ↔ q' h；hp : p ↔ p'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b

--- 原说明 ---
See `IsEmpty.exists_iff` for the `False` version of `exists_true_left`.
-/
theorem forall_prop_congr {p p' : Prop} {q q' : p → Prop} (hq : ∀ h, q h ↔ q' h) (hp : p ↔ p') :
    (∀ h, q h) ↔ ∀ h : p', q' (hp.2 h) :=
  ⟨fun h1 h2 ↦ (hq _).1 (h1 (hp.2 h2)), fun h1 h2 ↦ (hq _).2 (h1 (hp.1 h2))⟩
/-
**forall_prop_congr'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_prop_congr' {p p' : Prop} {q q' : p -> Prop} (hq : forall h, q h ↔ 
q' h) (hp : p ↔ p') : (forall h, q h) = forall h : p', q' (hp.2 h)
参数：hq : forall h, q h ↔ q' h；hp : p ↔ p'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `forall_prop_congr`：forall_prop_congr {p p' : Prop} {q q' : p -> Prop} (h
q : forall h, q h ↔ q' h) (hp : p ↔ p') : (forall h, q h) ↔ forall h : p', q' (h
p.2 h)
-/
theorem forall_prop_congr' {p p' : Prop} {q q' : p → Prop} (hq : ∀ h, q h ↔ q' h) (hp : p ↔ p') :
    (∀ h, q h) = ∀ h : p', q' (hp.2 h) :=
  propext (forall_prop_congr hq hp)
/-
**imp_congr_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：imp_congr_eq {a b c d : Prop} (h₁ : a = c) (h₂ : b = d) : (a -> b) = (c ->
 d)
参数：h₁ : a = c；h₂ : b = d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `imp_congr`：∀ {a b c d : Prop}, (a ↔ c) → (b ↔ d) → (a → b ↔ c → d)
· 使用定理 `Eq.to_iff`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
lemma imp_congr_eq {a b c d : Prop} (h₁ : a = c) (h₂ : b = d) : (a → b) = (c → d) :=
  propext (imp_congr h₁.to_iff h₂.to_iff)
/-
**imp_congr_ctx_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：imp_congr_ctx_eq {a b c d : Prop} (h₁ : a = c) (h₂ : c -> b = d) : (a -> b
) = (c -> d)
参数：h₁ : a = c；h₂ : c -> b = d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `imp_congr_ctx`：∀ {a b c d : Prop}, (a ↔ c) → (c → (b ↔ d)) → (a → b ↔ c 
→ d)
· 使用定理 `Eq.to_iff`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
lemma imp_congr_ctx_eq {a b c d : Prop} (h₁ : a = c) (h₂ : c → b = d) : (a → b) = (c → d) :=
  propext (imp_congr_ctx h₁.to_iff fun hc ↦ (h₂ hc).to_iff)
/-
**eq_true_intro** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_true_intro {a : Prop} (h : a) : a = True
参数：h : a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iff_true_intro`：∀ {a : Prop}, a → (a ↔ True)
-/
lemma eq_true_intro {a : Prop} (h : a) : a = True := propext (iff_true_intro h)
/-
**eq_false_intro** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_false_intro {a : Prop} (h : ¬a) : a = False
参数：h : ¬a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iff_false_intro`：∀ {a : Prop}, ¬a → (a ↔ False)
-/
lemma eq_false_intro {a : Prop} (h : ¬a) : a = False := propext (iff_false_intro h)

-- FIXME: `alias` creates `def Iff.eq := propext` instead of `lemma Iff.eq := propext`
alias Iff.eq := propext
/-
**iff_eq_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iff_eq_eq {a b : Prop} : (a ↔ b) = (a = b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.to_iff`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
lemma iff_eq_eq {a b : Prop} : (a ↔ b) = (a = b) := propext ⟨propext, Eq.to_iff⟩

-- They were not used in Lean 3 and there are already lemmas with those names in Lean 4

/-- See `IsEmpty.forall_iff` for the `False` version. -/
/-
**forall_true_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (p : True → Prop), (∀ (x : True), p x) ↔ p True.intro
参数：p : True → Prop；∀ (x : True), p x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_prop_of_true`：∀ {p : Prop} {q : p → Prop} (h : p), (∀ (h' : p), q
 h') ↔ q h

--- 原说明 ---
See `IsEmpty.forall_iff` for the `False` version.
-/
@[simp] theorem forall_true_left (p : True → Prop) : (∀ x, p x) ↔ p True.intro :=
  forall_prop_of_true _

@[simp]
/-
**Subsingleton.forall** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Subsingleton.forall₂_iff {ι : Sort*} [Subsingleton ι] (P : ι → ι → Prop) :
    (∀ i j, P i j) ↔ (∀ i, P i i) := by
  refine forall_congr' fun i ↦ ?_
  have : Nonempty ι := ⟨i⟩
  simp [Subsingleton.elim _ i]

end Quantifiers

/-! ### Classical lemmas -/

namespace Classical

-- use shortened names to avoid conflict when classical namespace is open.
/-- Any prop `p` is decidable classically. A shorthand for `Classical.propDecidable`. -/
@[instance_reducible]
/-
**Classical.dec** 是 Mathlib 中的一个定义，位于命名空间 `Classical`。
形式化陈述：dec (p : Prop) : Decidable p
参数：p : Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any prop `p` is decidable classically. A shorthand for `Classical.propDecidable`
.
-/
noncomputable def dec (p : Prop) : Decidable p := by infer_instance

variable {α : Sort*}

/-- Any predicate `p` is decidable classically. -/
@[instance_reducible]
/-
**Classical.decPred** 是 Mathlib 中的一个定义，位于命名空间 `Classical`。
形式化陈述：decPred (p : α -> Prop) : DecidablePred p
参数：p : α -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any predicate `p` is decidable classically.
-/
noncomputable def decPred (p : α → Prop) : DecidablePred p := by infer_instance

/-- Any relation `p` is decidable classically. -/
@[instance_reducible]
/-
**Classical.decRel** 是 Mathlib 中的一个定义，位于命名空间 `Classical`。
形式化陈述：decRel (p : α -> α -> Prop) : DecidableRel p
参数：p : α -> α -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any relation `p` is decidable classically.
-/
noncomputable def decRel (p : α → α → Prop) : DecidableRel p := by infer_instance

/-- Any type `α` has decidable equality classically. -/
@[instance_reducible]
/-
**Classical.decEq** 是 Mathlib 中的一个定义，位于命名空间 `Classical`。
形式化陈述：decEq (α : Sort*) : DecidableEq α
参数：α : Sort*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any type `α` has decidable equality classically.
-/
noncomputable def decEq (α : Sort*) : DecidableEq α := by infer_instance

/-- Construct a function from a default value `H0`, and a function to use if there exists a value
satisfying the predicate. -/
/-
**Classical.existsCases** 是 Mathlib 中的一个定义，位于命名空间 `Classical`。
形式化陈述：existsCases {α C : Sort*} {p : α -> Prop} (H0 : C) (H : forall a, p a -> C
) : C
参数：H0 : C；H : forall a, p a -> C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
Construct a function from a default value `H0`, and a function to use if there e
xists a value
satisfying the predicate.
-/
noncomputable def existsCases {α C : Sort*} {p : α → Prop} (H0 : C) (H : ∀ a, p a → C) : C :=
  if h : ∃ a, p a then H (Classical.choose h) (Classical.choose_spec h) else H0
/-
**Classical.some_spec** 是 Mathlib 中的一个定理，位于命名空间 `Classical`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem some_spec₂ {α : Sort*} {p : α → Prop} {h : ∃ a, p a} (q : α → Prop)
    (hpq : ∀ a, p a → q a) : q (choose h) := hpq _ <| choose_spec _

/-- A version of `byContradiction` that uses types instead of propositions. -/
/-
**Classical.byContradiction'** 是 Mathlib 中的一个定义，位于命名空间 `Classical`。
形式化陈述：{α : Sort u_2} → (¬∀ (a : α), False) → α
参数：¬∀ (a : α), False。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `byContradiction` that uses types instead of propositions.
-/
protected noncomputable def byContradiction' {α : Sort*} (H : ¬(α → False)) : α :=
  Classical.choice <| (peirce _ False) fun h ↦ (H fun a ↦ h ⟨a⟩).elim

/-- `Classical.byContradiction'` is equivalent to lean's axiom `Classical.choice`. -/
/-
**Classical.choice_of_byContradiction'** 是 Mathlib 中的一个定义，位于命名空间 `Classical`。
形式化陈述：choice_of_byContradiction' {α : Sort*} (contra : ¬(α -> False) -> α) : Non
empty α -> α
参数：contra : ¬(α -> False) -> α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p

--- 原说明 ---
`Classical.byContradiction'` is equivalent to lean's axiom `Classical.choice`.
-/
def choice_of_byContradiction' {α : Sort*} (contra : ¬(α → False) → α) : Nonempty α → α :=
  fun H ↦ contra H.elim

-- This can be removed after https://github.com/leanprover/lean4/pull/11316
-- arrives in a release candidate.
grind_pattern Exists.choose_spec => P.choose
/-
**Classical.choose_eq** 是 Mathlib 中的一个定理，位于命名空间 `Classical`。
形式化陈述：∀ {α : Sort u_1} (a : α), ⋯.choose = a
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
@[simp] lemma choose_eq (a : α) : @Exists.choose _ (· = a) ⟨a, rfl⟩ = a := @choose_spec _ (· = a) _

@[simp]
/-
**Classical.choose_eq'** 是 Mathlib 中的一个引理，位于命名空间 `Classical`。
形式化陈述：choose_eq' (a : α) : @Exists.choose _ (a = ·) ⟨a, rfl⟩ = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma choose_eq' (a : α) : @Exists.choose _ (a = ·) ⟨a, rfl⟩ = a :=
  (@choose_spec _ (a = ·) _).symm

alias axiom_of_choice := axiomOfChoice -- TODO: remove? rename in core?
alias by_cases := byCases -- TODO: remove? rename in core?
alias by_contradiction := byContradiction -- TODO: remove? rename in core?

-- The remaining theorems in this section were ported from Lean 3,
-- but are currently unused in Mathlib, so have been deprecated.
-- If any are being used downstream, please remove the deprecation.

alias prop_complete := propComplete -- TODO: remove? rename in core?

end Classical

/-- This function has the same type as `Exists.recOn`, and can be used to case on an equality,
but `Exists.recOn` can only eliminate into Prop, while this version eliminates into any universe
using the axiom of choice. -/
/-
**Exists.classicalRecOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Exists.classicalRecOn {α : Sort*} {p : α -> Prop} (h : exists a, p a) {C :
 Sort*} (H : forall a, p a -> C) : C
参数：h : exists a, p a；H : forall a, p a -> C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
This function has the same type as `Exists.recOn`, and can be used to case on an
 equality,
but `Exists.recOn` can only eliminate into Prop, while this version eliminates i
nto any universe
using the axiom of choice.
-/
noncomputable def Exists.classicalRecOn {α : Sort*} {p : α → Prop} (h : ∃ a, p a)
    {C : Sort*} (H : ∀ a, p a → C) : C :=
  H (Classical.choose h) (Classical.choose_spec h)

/-! ### Declarations about bounded quantifiers -/
section BoundedQuantifiers

variable {α : Sort*} {r p q : α → Prop} {P Q : ∀ x, p x → Prop}

/-
**bex_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bex_def : (exists (x : _) (_ : p x), q x) ↔ exists x, p x ∧ q x
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bex_def : (∃ (x : _) (_ : p x), q x) ↔ ∃ x, p x ∧ q x :=
  ⟨fun ⟨x, px, qx⟩ ↦ ⟨x, px, qx⟩, fun ⟨x, px, qx⟩ ↦ ⟨x, px, qx⟩⟩
/-
**BEx.elim** 是 Mathlib 中的一个定理，位于命名空间 `BEx`。
形式化陈述：∀ {α : Sort u_1} {p : α → Prop} {P : (x : α) → p x → Prop} {b : Prop},   (
∃ x, ∃ (h : p x), P x h) → (∀ (a : α) (h : p a), P a h → b) → b
参数：x : α；∃ x, ∃ (h : p x), P x h；∀ (a : α) (h : p a), P a h → b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem BEx.elim {b : Prop} : (∃ x h, P x h) → (∀ a h, P a h → b) → b
  | ⟨a, h₁, h₂⟩, h' => h' a h₁ h₂
/-
**BEx.intro** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：BEx.intro (a : α) (h₁ : p a) (h₂ : P a h₁) : exists (x : _) (h : p x), P x
 h
参数：a : α；h₁ : p a；h₂ : P a h₁。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem BEx.intro (a : α) (h₁ : p a) (h₂ : P a h₁) : ∃ (x : _) (h : p x), P x h :=
  ⟨a, h₁, h₂⟩
/-
**BAll.imp_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：BAll.imp_right (H : forall x h, P x h -> Q x h) (h₁ : forall x h, P x h) (
x h) : Q x h
参数：H : forall x h, P x h -> Q x h；h₁ : forall x h, P x h；x h。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem BAll.imp_right (H : ∀ x h, P x h → Q x h) (h₁ : ∀ x h, P x h) (x h) : Q x h :=
  H _ _ <| h₁ _ _
/-
**BEx.imp_right** 是 Mathlib 中的一个定理，位于命名空间 `BEx`。
形式化陈述：∀ {α : Sort u_1} {p : α → Prop} {P Q : (x : α) → p x → Prop},   (∀ (x : α)
 (h : p x), P x h → Q x h) → (∃ x, ∃ (h : p x), P x h) → ∃ x, ∃ (h : p x), Q x h
参数：x : α；∀ (x : α) (h : p x), P x h → Q x h；∃ x, ∃ (h : p x), P x h；h : p x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem BEx.imp_right (H : ∀ x h, P x h → Q x h) : (∃ x h, P x h) → ∃ x h, Q x h
  | ⟨_, _, h'⟩ => ⟨_, _, H _ _ h'⟩
/-
**BAll.imp_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：BAll.imp_left (H : forall x, p x -> q x) (h₁ : forall x, q x -> r x) (x) (
h : p x) : r x
参数：H : forall x, p x -> q x；h₁ : forall x, q x -> r x；x；h : p x。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem BAll.imp_left (H : ∀ x, p x → q x) (h₁ : ∀ x, q x → r x) (x) (h : p x) : r x :=
  h₁ _ <| H _ h
/-
**BEx.imp_left** 是 Mathlib 中的一个定理，位于命名空间 `BEx`。
形式化陈述：∀ {α : Sort u_1} {r p q : α → Prop}, (∀ (x : α), p x → q x) → (∃ x, ∃ (_ :
 p x), r x) → ∃ x, ∃ (_ : q x), r x
参数：∀ (x : α), p x → q x；∃ x, ∃ (_ : p x), r x；_ : q x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem BEx.imp_left (H : ∀ x, p x → q x) : (∃ (x : _) (_ : p x), r x) → ∃ (x : _) (_ : q x), r x
  | ⟨x, hp, hr⟩ => ⟨x, H _ hp, hr⟩
/-
**exists_mem_of_exists** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (x : α), p x) → (∃ x, q x) → ∃ x, ∃ 
(_ : p x), q x
参数：∀ (x : α), p x；∃ x, q x；_ : p x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_mem_of_exists (H : ∀ x, p x) : (∃ x, q x) → ∃ (x : _) (_ : p x), q x
  | ⟨x, hq⟩ => ⟨x, H x, hq⟩
/-
**exists_of_exists_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Sort u_1} {p q : α → Prop}, (∃ x, ∃ (_ : p x), q x) → ∃ x, q x
参数：∃ x, ∃ (_ : p x), q x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_of_exists_mem : (∃ (x : _) (_ : p x), q x) → ∃ x, q x
  | ⟨x, _, hq⟩ => ⟨x, hq⟩
/-
**not_exists_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_exists_mem : (¬exists x h, P x h) ↔ forall x h, ¬P x h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists₂_imp`：∀ {α : Sort u_1} {p : α → Prop} {b : Prop} {P : (x : α) → p
 x → Prop},   (∃ x, ∃ (h : p x), P x h) → b ↔ ∀ (x : α) (h : p x), P x h → b
-/
theorem not_exists_mem : (¬∃ x h, P x h) ↔ ∀ x h, ¬P x h := exists₂_imp
/-
**not_forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem not_forall₂_of_exists₂_not : (∃ x h, ¬P x h) → ¬∀ x h, P x h
  | ⟨x, h, hp⟩, al => hp <| al x h

-- See Note [decidable namespace]
/-
**Decidable.not_forall** 是 Mathlib 中的一个定理，位于命名空间 `Decidable`。
形式化陈述：∀ {α : Sort u_1} {p : α → Prop} [Decidable (∃ x, ¬p x)] [(x : α) → Decidab
le (p x)], (¬∀ (x : α), p x) ↔ ∃ x, ¬p x
参数：∃ x, ¬p x；x : α；p x；¬∀ (x : α), p x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.not_imp_symm`：∀ {a b : Prop} [Decidable a], (¬a → b) → ¬b → a
· 使用定理 `not_forall_of_exists_not`：∀ {α : Sort u_1} {p : α → Prop}, (∃ x, ¬p x) →
 ¬∀ (x : α), p x
-/
protected theorem Decidable.not_forall₂ [Decidable (∃ x h, ¬P x h)] [∀ x h, Decidable (P x h)] :
    (¬∀ x h, P x h) ↔ ∃ x h, ¬P x h :=
  ⟨Not.decidable_imp_symm fun nx x h ↦ nx.decidable_imp_symm
    fun h' ↦ ⟨x, h, h'⟩, not_forall₂_of_exists₂_not⟩
/-
**not_forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem not_forall₂ : (¬∀ x h, P x h) ↔ ∃ x h, ¬P x h :=
  open scoped Classical in Decidable.not_forall₂
/-
**forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall₂_and : (∀ x h, P x h ∧ Q x h) ↔ (∀ x h, P x h) ∧ ∀ x h, Q x h :=
  Iff.trans (forall_congr' fun _ ↦ forall_and) forall_and
/-
**forall_and_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_and_left [Nonempty α] (q : Prop) (p : α -> Prop) : (forall x, q ∧ p
 x) ↔ (q ∧ forall x, p x)
参数：q : Prop；p : α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_and`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (x : α), p x ∧ q x) ↔ 
(∀ (x : α), p x) ∧ ∀ (x : α), q x
· 使用定理 `forall_const`：∀ {b : Prop} (α : Sort u_1) [i : Nonempty α], (∀ (a : α), 
b) ↔ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem forall_and_left [Nonempty α] (q : Prop) (p : α → Prop) :
    (∀ x, q ∧ p x) ↔ (q ∧ ∀ x, p x) := by rw [forall_and, forall_const]
/-
**forall_and_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_and_right [Nonempty α] (p : α -> Prop) (q : Prop) : (forall x, p x 
∧ q) ↔ (forall x, p x) ∧ q
参数：p : α -> Prop；q : Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_and`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (x : α), p x ∧ q x) ↔ 
(∀ (x : α), p x) ∧ ∀ (x : α), q x
· 使用定理 `forall_const`：∀ {b : Prop} (α : Sort u_1) [i : Nonempty α], (∀ (a : α), 
b) ↔ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem forall_and_right [Nonempty α] (p : α → Prop) (q : Prop) :
    (∀ x, p x ∧ q) ↔ (∀ x, p x) ∧ q := by rw [forall_and, forall_const]
/-
**exists_mem_or** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_mem_or : (exists x h, P x h ∨ Q x h) ↔ (exists x h, P x h) ∨ exists
 x h, Q x h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `exists_or`：∀ {α : Sort u_1} {p q : α → Prop}, (∃ x, p x ∨ q x) ↔ (∃ x, p
 x) ∨ ∃ x, q x
-/
theorem exists_mem_or : (∃ x h, P x h ∨ Q x h) ↔ (∃ x h, P x h) ∨ ∃ x h, Q x h :=
  Iff.trans (exists_congr fun _ ↦ exists_or) exists_or
/-
**forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall₂_or_left : (∀ x, p x ∨ q x → r x) ↔ (∀ x, p x → r x) ∧ ∀ x, q x → r x :=
  Iff.trans (forall_congr' fun _ ↦ or_imp) forall_and
/-
**exists_mem_or_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_mem_or_left : (exists (x : _) (_ : p x ∨ q x), r x) ↔ (exists (x : 
_) (_ : p x), r x) ∨ exists (x : _) (_ : q x), r x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `or_and_right`：∀ {a b c : Prop}, (a ∨ b) ∧ c ↔ a ∧ c ∨ b ∧ c
· 使用定理 `exists_or`：∀ {α : Sort u_1} {p q : α → Prop}, (∃ x, p x ∨ q x) ↔ (∃ x, p
 x) ∨ ∃ x, q x
-/
theorem exists_mem_or_left :
    (∃ (x : _) (_ : p x ∨ q x), r x) ↔ (∃ (x : _) (_ : p x), r x) ∨ ∃ (x : _) (_ : q x), r x := by
  simp only [exists_prop]
  exact Iff.trans (exists_congr fun x ↦ or_and_right) exists_or

end BoundedQuantifiers

section ite

variable {α : Sort*} {σ : α → Sort*} {P Q R : Prop} [Decidable P]
  {a b c : α} {A : P → α} {B : ¬P → α}

/-
**dite_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dite_eq_iff : dite P A B = c ↔ (exists h, A h = c) ∨ exists h, B h = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem dite_eq_iff : dite P A B = c ↔ (∃ h, A h = c) ∨ ∃ h, B h = c := by
  by_cases P <;> simp [*, exists_prop_of_true, exists_prop_of_false]
/-
**ite_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ite_eq_iff : ite P a b = c ↔ P ∧ a = c ∨ ¬P ∧ b = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `dite_eq_iff`：dite_eq_iff : dite P A B = c ↔ (exists h, A h = c) ∨ exists
 h, B h = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `exists_prop`：∀ {b a : Prop}, (∃ (_ : a), b) ↔ a ∧ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ite_eq_iff : ite P a b = c ↔ P ∧ a = c ∨ ¬P ∧ b = c :=
  dite_eq_iff.trans <| by rw [exists_prop, exists_prop]
/-
**eq_ite_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_ite_iff : a = ite P b c ↔ P ∧ a = b ∨ ¬P ∧ a = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `ite_eq_iff`：ite_eq_iff : ite P a b = c ↔ P ∧ a = c ∨ ¬P ∧ b = c
· 使用定理 `Iff.or`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∨ b ↔ c ∨ d)
· 使用定理 `Iff.and`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_ite_iff : a = ite P b c ↔ P ∧ a = b ∨ ¬P ∧ a = c :=
  eq_comm.trans <| ite_eq_iff.trans <| (Iff.rfl.and eq_comm).or (Iff.rfl.and eq_comm)
/-
**dite_eq_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dite_eq_iff' : dite P A B = c ↔ (forall h, A h = c) ∧ forall h, B h = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem dite_eq_iff' : dite P A B = c ↔ (∀ h, A h = c) ∧ ∀ h, B h = c :=
  ⟨fun he ↦ ⟨fun h ↦ (dif_pos h).symm.trans he, fun h ↦ (dif_neg h).symm.trans he⟩, fun he ↦
    (em P).elim (fun h ↦ (dif_pos h).trans <| he.1 h) fun h ↦ (dif_neg h).trans <| he.2 h⟩
/-
**ite_eq_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ite_eq_iff' : ite P a b = c ↔ (P -> a = c) ∧ (¬P -> b = c)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dite_eq_iff'`：dite_eq_iff' : dite P A B = c ↔ (forall h, A h = c) ∧ fora
ll h, B h = c
-/
theorem ite_eq_iff' : ite P a b = c ↔ (P → a = c) ∧ (¬P → b = c) := dite_eq_iff'
/-
**dite_ne_left_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dite_ne_left_iff : dite P (fun _ => a) B != a ↔ exists h, a != B h
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dite_ne_left_iff : dite P (fun _ ↦ a) B ≠ a ↔ ∃ h, a ≠ B h := by
  grind
/-
**dite_ne_right_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dite_ne_right_iff : (dite P A fun _ => b) != b ↔ exists h, A h != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem dite_ne_right_iff : (dite P A fun _ ↦ b) ≠ b ↔ ∃ h, A h ≠ b := by
  simp only [Ne, dite_eq_right_iff, not_forall]
/-
**ite_ne_left_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ite_ne_left_iff : ite P a b != a ↔ ¬P ∧ a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `dite_ne_left_iff`：dite_ne_left_iff : dite P (fun _ => a) B != a ↔ exists
 h, a != B h
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `exists_prop`：∀ {b a : Prop}, (∃ (_ : a), b) ↔ a ∧ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ite_ne_left_iff : ite P a b ≠ a ↔ ¬P ∧ a ≠ b :=
  dite_ne_left_iff.trans <| by rw [exists_prop]
/-
**ite_ne_right_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ite_ne_right_iff : ite P a b != b ↔ P ∧ a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `dite_ne_right_iff`：dite_ne_right_iff : (dite P A fun _ => b) != b ↔ exis
ts h, A h != b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `exists_prop`：∀ {b a : Prop}, (∃ (_ : a), b) ↔ a ∧ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ite_ne_right_iff : ite P a b ≠ b ↔ P ∧ a ≠ b :=
  dite_ne_right_iff.trans <| by rw [exists_prop]
/-
**Ne.dite_eq_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ne`。
形式化陈述：∀ {α : Sort u_1} {P : Prop} [inst : Decidable P] {a : α} {B : ¬P → α},   (
∀ (h : ¬P), a ≠ B h) → (dite P (fun x => a) B = a ↔ P)
参数：∀ (h : ¬P), a ≠ B h；dite P (fun x => a) B = a ↔ P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `dite_eq_left_iff`：∀ {α : Sort u_1} {p : Prop} [inst : Decidable p] {x : 
α} {y : ¬p → α},   (if h : p then x else y h) = x ↔ ∀ (h : ¬p), y h = x
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem Ne.dite_eq_left_iff (h : ∀ h, a ≠ B h) : dite P (fun _ ↦ a) B = a ↔ P :=
  dite_eq_left_iff.trans ⟨fun H ↦ of_not_not fun h' ↦ h h' (H h').symm, fun h H ↦ (H h).elim⟩
/-
**Ne.dite_eq_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ne`。
形式化陈述：∀ {α : Sort u_1} {P : Prop} [inst : Decidable P] {b : α} {A : P → α},   (∀
 (h : P), A h ≠ b) → ((dite P A fun x => b) = b ↔ ¬P)
参数：∀ (h : P), A h ≠ b；(dite P A fun x => b) = b ↔ ¬P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `dite_eq_right_iff`：∀ {α : Sort u_1} {p : Prop} [inst : Decidable p] {x :
 p → α} {y : α},   (if h : p then x h else y) = y ↔ ∀ (h : p), x h = y
-/
protected theorem Ne.dite_eq_right_iff (h : ∀ h, A h ≠ b) : (dite P A fun _ ↦ b) = b ↔ ¬P :=
  dite_eq_right_iff.trans ⟨fun H h' ↦ h h' (H h'), fun h' H ↦ (h' H).elim⟩
/-
**Ne.ite_eq_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ne`。
形式化陈述：∀ {α : Sort u_1} {P : Prop} [inst : Decidable P] {a b : α}, a ≠ b → ((if P
 then a else b) = a ↔ P)
参数：(if P then a else b) = a ↔ P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.dite_eq_left_iff`：∀ {α : Sort u_1} {P : Prop} [inst : Decidable P] {a
 : α} {B : ¬P → α},   (∀ (h : ¬P), a ≠ B h) → (dite P (fun x => a) B = a ↔ P)
-/
protected theorem Ne.ite_eq_left_iff (h : a ≠ b) : ite P a b = a ↔ P :=
  Ne.dite_eq_left_iff fun _ ↦ h
/-
**Ne.ite_eq_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ne`。
形式化陈述：∀ {α : Sort u_1} {P : Prop} [inst : Decidable P] {a b : α}, a ≠ b → ((if P
 then a else b) = b ↔ ¬P)
参数：(if P then a else b) = b ↔ ¬P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.dite_eq_right_iff`：∀ {α : Sort u_1} {P : Prop} [inst : Decidable P] {
b : α} {A : P → α},   (∀ (h : P), A h ≠ b) → ((dite P A fun x => b) = b ↔ ¬P)
-/
protected theorem Ne.ite_eq_right_iff (h : a ≠ b) : ite P a b = b ↔ ¬P :=
  Ne.dite_eq_right_iff fun _ ↦ h
/-
**Ne.dite_ne_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ne`。
形式化陈述：∀ {α : Sort u_1} {P : Prop} [inst : Decidable P] {a : α} {B : ¬P → α},   (
∀ (h : ¬P), a ≠ B h) → (dite P (fun x => a) B ≠ a ↔ ¬P)
参数：∀ (h : ¬P), a ≠ B h；dite P (fun x => a) B ≠ a ↔ ¬P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `dite_ne_left_iff`：dite_ne_left_iff : dite P (fun _ => a) B != a ↔ exists
 h, a != B h
· 使用定理 `exists_iff_of_forall`：exists_iff_of_forall {p : Prop} {q : p -> Prop} (h
 : forall h, q h) : (exists h, q h) ↔ p
-/
protected theorem Ne.dite_ne_left_iff (h : ∀ h, a ≠ B h) : dite P (fun _ ↦ a) B ≠ a ↔ ¬P :=
  dite_ne_left_iff.trans <| exists_iff_of_forall h
/-
**Ne.dite_ne_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ne`。
形式化陈述：∀ {α : Sort u_1} {P : Prop} [inst : Decidable P] {b : α} {A : P → α},   (∀
 (h : P), A h ≠ b) → ((dite P A fun x => b) ≠ b ↔ P)
参数：∀ (h : P), A h ≠ b；(dite P A fun x => b) ≠ b ↔ P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `dite_ne_right_iff`：dite_ne_right_iff : (dite P A fun _ => b) != b ↔ exis
ts h, A h != b
· 使用定理 `exists_iff_of_forall`：exists_iff_of_forall {p : Prop} {q : p -> Prop} (h
 : forall h, q h) : (exists h, q h) ↔ p
-/
protected theorem Ne.dite_ne_right_iff (h : ∀ h, A h ≠ b) : (dite P A fun _ ↦ b) ≠ b ↔ P :=
  dite_ne_right_iff.trans <| exists_iff_of_forall h
/-
**Ne.ite_ne_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ne`。
形式化陈述：∀ {α : Sort u_1} {P : Prop} [inst : Decidable P] {a b : α}, a ≠ b → ((if P
 then a else b) ≠ a ↔ ¬P)
参数：(if P then a else b) ≠ a ↔ ¬P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.dite_ne_left_iff`：∀ {α : Sort u_1} {P : Prop} [inst : Decidable P] {a
 : α} {B : ¬P → α},   (∀ (h : ¬P), a ≠ B h) → (dite P (fun x => a) B ≠ a ↔ ¬P)
-/
protected theorem Ne.ite_ne_left_iff (h : a ≠ b) : ite P a b ≠ a ↔ ¬P :=
  Ne.dite_ne_left_iff fun _ ↦ h
/-
**Ne.ite_ne_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ne`。
形式化陈述：∀ {α : Sort u_1} {P : Prop} [inst : Decidable P] {a b : α}, a ≠ b → ((if P
 then a else b) ≠ b ↔ P)
参数：(if P then a else b) ≠ b ↔ P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.dite_ne_right_iff`：∀ {α : Sort u_1} {P : Prop} [inst : Decidable P] {
b : α} {A : P → α},   (∀ (h : P), A h ≠ b) → ((dite P A fun x => b) ≠ b ↔ P)
-/
protected theorem Ne.ite_ne_right_iff (h : a ≠ b) : ite P a b ≠ b ↔ P :=
  Ne.dite_ne_right_iff fun _ ↦ h

variable (P Q a b)
/-
**dite_eq_or_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dite_eq_or_eq : (exists h, dite P A B = A h) ∨ exists h, dite P A B = B h
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem dite_eq_or_eq : (∃ h, dite P A B = A h) ∨ ∃ h, dite P A B = B h :=
  if h : _ then .inl ⟨h, dif_pos h⟩ else .inr ⟨h, dif_neg h⟩
/-
**ite_eq_or_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ite_eq_or_eq : ite P a b = a ∨ ite P a b = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem ite_eq_or_eq : ite P a b = a ∨ ite P a b = b :=
  if h : _ then .inl (if_pos h) else .inr (if_neg h)

/-- A two-argument function applied to two `dite`s is a `dite` of that two-argument function
applied to each of the branches. -/
/-
**apply_dite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst : Decidable P
] (x : P → α) (y : ¬P → α),   f (dite P x y) = if h : P then f (x h) else f (y h
)
参数：f : α → β；P : Prop；x : P → α；y : ¬P → α；dite P x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯

--- 原说明 ---
A two-argument function applied to two `dite`s is a `dite` of that two-argument 
function
applied to each of the branches.
-/
theorem apply_dite₂ {α β γ : Sort*} (f : α → β → γ) (P : Prop) [Decidable P]
    (a : P → α) (b : ¬P → α) (c : P → β) (d : ¬P → β) :
    f (dite P a b) (dite P c d) = dite P (fun h ↦ f (a h) (c h)) fun h ↦ f (b h) (d h) := by
  by_cases h : P <;> simp [h]

/-- A two-argument function applied to two `ite`s is a `ite` of that two-argument function
applied to each of the branches. -/
/-
**apply_ite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst : Decidable P
] (x y : α),   f (if P then x else y) = if P then f x else f y
参数：f : α → β；P : Prop；x y : α；if P then x else y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `apply_dite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst
 : Decidable P] (x : P → α) (y : ¬P → α),   f (dite P x y) = if h : P then f (x 
…

--- 原说明 ---
A two-argument function applied to two `ite`s is a `ite` of that two-argument fu
nction
applied to each of the branches.
-/
theorem apply_ite₂ {α β γ : Sort*} (f : α → β → γ) (P : Prop) [Decidable P] (a b : α) (c d : β) :
    f (ite P a b) (ite P c d) = ite P (f a c) (f b d) :=
  apply_dite₂ f P (fun _ ↦ a) (fun _ ↦ b) (fun _ ↦ c) fun _ ↦ d

/-- A 'dite' producing a `Pi` type `Π a, σ a`, applied to a value `a : α` is a `dite` that applies
either branch to `a`. -/
/-
**dite_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dite_apply (f : P -> forall a, σ a) (g : ¬P -> forall a, σ a) (a : α) : (d
ite P f g) a = dite P (fun h => f h a) fun h => g h a
参数：f : P -> forall a, σ a；g : ¬P -> forall a, σ a；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯

--- 原说明 ---
A 'dite' producing a `Pi` type `Π a, σ a`, applied to a value `a : α` is a `dite
` that applies
either branch to `a`.
-/
theorem dite_apply (f : P → ∀ a, σ a) (g : ¬P → ∀ a, σ a) (a : α) :
    (dite P f g) a = dite P (fun h ↦ f h a) fun h ↦ g h a := by by_cases h : P <;> simp [h]

/-- A 'ite' producing a `Pi` type `Π a, σ a`, applied to a value `a : α` is a `ite` that applies
either branch to `a`. -/
/-
**ite_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ite_apply (f g : forall a, σ a) (a : α) : (ite P f g) a = ite P (f a) (g a
)
参数：f g : forall a, σ a；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dite_apply`：dite_apply (f : P -> forall a, σ a) (g : ¬P -> forall a, σ a
) (a : α) : (dite P f g) a = dite P (fun h => f h a) fun h => g h a

--- 原说明 ---
A 'ite' producing a `Pi` type `Π a, σ a`, applied to a value `a : α` is a `ite` 
that applies
either branch to `a`.
-/
theorem ite_apply (f g : ∀ a, σ a) (a : α) : (ite P f g) a = ite P (f a) (g a) :=
  dite_apply P (fun _ ↦ f) (fun _ ↦ g) a
/-
**apply_ite_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：apply_ite_left {α β γ : Sort*} (f : α -> β -> γ) (P : Prop) [Decidable P] 
(x y : α) (z : β) : f (if P then x else y) z = if P then f x z else f y z
参数：f : α -> β -> γ；P : Prop；x y : α；z : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem apply_ite_left {α β γ : Sort*} (f : α → β → γ) (P : Prop) [Decidable P]
    (x y : α) (z : β) : f (if P then x else y) z = if P then f x z else f y z := by grind

section
variable [Decidable Q]

/-
**ite_and** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ite_and : ite (P ∧ Q) a b = ite P (ite Q a b) b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem ite_and : ite (P ∧ Q) a b = ite P (ite Q a b) b := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]
/-
**ite_or** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ite_or : ite (P ∨ Q) a b = ite P a (ite Q a b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
-/
theorem ite_or : ite (P ∨ Q) a b = ite P a (ite Q a b) := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]
/-
**dite_dite_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dite_dite_comm {B : Q -> α} {C : ¬P -> ¬Q -> α} (h : P -> ¬Q) : (if p : P 
then A p else if q : Q then B q else C p q) = if q : Q then B q else if p : P th
en A p else C p q
参数：h : P -> ¬Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dite_dite_comm {B : Q → α} {C : ¬P → ¬Q → α} (h : P → ¬Q) :
    (if p : P then A p else if q : Q then B q else C p q) =
     if q : Q then B q else if p : P then A p else C p q := by
  grind
/-
**ite_ite_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ite_ite_comm (h : P -> ¬Q) : (if P then a else if Q then b else c) = if Q 
then b else if P then a else c
参数：h : P -> ¬Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dite_dite_comm`：dite_dite_comm {B : Q -> α} {C : ¬P -> ¬Q -> α} (h : P -
> ¬Q) : (if p : P then A p else if q : Q then B q else C p q) = if q : Q then B 
q el…
-/
theorem ite_ite_comm (h : P → ¬Q) :
    (if P then a else if Q then b else c) =
     if Q then b else if P then a else c :=
  dite_dite_comm P Q h

end

variable {P Q}

/-
**ite_prop_iff_or** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ite_prop_iff_or : (if P then Q else R) ↔ (P ∧ Q ∨ ¬P ∧ R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem ite_prop_iff_or : (if P then Q else R) ↔ (P ∧ Q ∨ ¬P ∧ R) := by
  by_cases p : P <;> simp [p]
/-
**dite_prop_iff_or** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dite_prop_iff_or {Q : P -> Prop} {R : ¬P -> Prop} : dite P Q R ↔ (exists p
, Q p) ∨ (exists p, R p)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem dite_prop_iff_or {Q : P → Prop} {R : ¬P → Prop} :
    dite P Q R ↔ (∃ p, Q p) ∨ (∃ p, R p) := by
  by_cases h : P <;> simp [h, exists_prop_of_false, exists_prop_of_true]

-- TODO make this a simp lemma in a future PR
/-
**ite_prop_iff_and** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ite_prop_iff_and : (if P then Q else R) ↔ ((P -> Q) ∧ (¬P -> R))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_implies`：∀ (p : Prop), (False → p) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem ite_prop_iff_and : (if P then Q else R) ↔ ((P → Q) ∧ (¬P → R)) := by
  by_cases p : P <;> simp [p]
/-
**dite_prop_iff_and** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dite_prop_iff_and {Q : P -> Prop} {R : ¬P -> Prop} : dite P Q R ↔ (forall 
h, Q h) ∧ (forall h, R h)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem dite_prop_iff_and {Q : P → Prop} {R : ¬P → Prop} :
    dite P Q R ↔ (∀ h, Q h) ∧ (∀ h, R h) := by
  by_cases h : P <;> simp [h, forall_prop_of_false, forall_prop_of_true]

section congr

variable [Decidable Q] {x y u v : α}

/-
**if_ctx_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：if_ctx_congr (h_c : P ↔ Q) (h_t : Q -> x = u) (h_e : ¬Q -> y = v) : ite P 
x y = ite Q u v
参数：h_c : P ↔ Q；h_t : Q -> x = u；h_e : ¬Q -> y = v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
-/
theorem if_ctx_congr (h_c : P ↔ Q) (h_t : Q → x = u) (h_e : ¬Q → y = v) : ite P x y = ite Q u v :=
  ite_congr h_c.eq h_t h_e
/-
**if_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：if_congr (h_c : P ↔ Q) (h_t : x = u) (h_e : y = v) : ite P x y = ite Q u v
参数：h_c : P ↔ Q；h_t : x = u；h_e : y = v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_ctx_congr`：if_ctx_congr (h_c : P ↔ Q) (h_t : Q -> x = u) (h_e : ¬Q ->
 y = v) : ite P x y = ite Q u v
-/
theorem if_congr (h_c : P ↔ Q) (h_t : x = u) (h_e : y = v) : ite P x y = ite Q u v :=
  if_ctx_congr h_c (fun _ ↦ h_t) (fun _ ↦ h_e)

end congr

/-
**Function.Injective.ite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.ite {α β : Sort*} {p : β -> Prop} [DecidablePred p] {g 
: β -> α} (hg : g.Injective) {f : β -> α} (hf : f.Injective) (h : forall x y, g 
x = f y -> x = y) : (fun x => if p x then g x else f x).Injective
参数：hg : g.Injective；hf : f.Injective；h : forall x y, g x = f y -> x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
-/
theorem Function.Injective.ite {α β : Sort*} {p : β → Prop} [DecidablePred p] {g : β → α}
    (hg : g.Injective) {f : β → α} (hf : f.Injective) (h : ∀ x y, g x = f y → x = y) :
    (fun x ↦ if p x then g x else f x).Injective :=
  fun x y _ ↦ by rcases em (p x) with (hx | hx) <;> rcases em (p y) with (hy | hy) <;> grind

end ite

/-! ### Membership -/

alias Membership.mem.ne_of_notMem := ne_of_mem_of_not_mem
alias Membership.mem.ne_of_notMem' := ne_of_mem_of_not_mem'

section Membership

variable {α β : Type*} [Membership α β] {p : Prop} [Decidable p]

/-
**mem_dite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_dite {a : α} {s : p -> β} {t : ¬p -> β} : (a in if h : p then s h else
 t h) ↔ (forall h, a in s h) ∧ (forall h, a in t h)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `forall_false`：∀ (p : False → Prop), (∀ (h : False), p h) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem mem_dite {a : α} {s : p → β} {t : ¬p → β} :
    (a ∈ if h : p then s h else t h) ↔ (∀ h, a ∈ s h) ∧ (∀ h, a ∈ t h) := by
  by_cases h : p <;> simp [h]
/-
**dite_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dite_mem {a : p -> α} {b : ¬p -> α} {s : β} : (if h : p then a h else b h)
 in s ↔ (forall h, a h in s) ∧ (forall h, b h in s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `forall_false`：∀ (p : False → Prop), (∀ (h : False), p h) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem dite_mem {a : p → α} {b : ¬p → α} {s : β} :
    (if h : p then a h else b h) ∈ s ↔ (∀ h, a h ∈ s) ∧ (∀ h, b h ∈ s) := by
  by_cases h : p <;> simp [h]
/-
**mem_ite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_ite {a : α} {s t : β} : (a in if p then s else t) ↔ (p -> a in s) ∧ (¬
p -> a in t)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_dite`：mem_dite {a : α} {s : p -> β} {t : ¬p -> β} : (a in if h : p t
hen s h else t h) ↔ (forall h, a in s h) ∧ (forall h, a in t h)
-/
theorem mem_ite {a : α} {s t : β} : (a ∈ if p then s else t) ↔ (p → a ∈ s) ∧ (¬p → a ∈ t) :=
  mem_dite
/-
**ite_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ite_mem {a b : α} {s : β} : (if p then a else b) in s ↔ (p -> a in s) ∧ (¬
p -> b in s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dite_mem`：dite_mem {a : p -> α} {b : ¬p -> α} {s : β} : (if h : p then a
 h else b h) in s ↔ (forall h, a h in s) ∧ (forall h, b h in s)
-/
theorem ite_mem {a b : α} {s : β} : (if p then a else b) ∈ s ↔ (p → a ∈ s) ∧ (¬p → b ∈ s) :=
  dite_mem

end Membership

/-
**not_beq_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_beq_of_ne {α : Type*} [BEq α] [LawfulBEq α] {a b : α} (ne : a != b) : 
¬(a == b)
参数：ne : a != b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LawfulBEq.eq_of_beq`：∀ {α : Type u} {inst : BEq α} [self : LawfulBEq α] 
{a b : α}, (a == b) = true → a = b
-/
theorem not_beq_of_ne {α : Type*} [BEq α] [LawfulBEq α] {a b : α} (ne : a ≠ b) : ¬(a == b) :=
  fun h => ne (eq_of_beq h)

alias beq_eq_decide := Bool.beq_eq_decide_eq
/-
**beq_eq_beq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : BEq α] [LawfulBEq α] [inst_2 : BEq
 β] [LawfulBEq β] {a₁ a₂ : α} {b₁ b₂ : β},   (a₁ == a₂) = (b₁ == b₂) ↔ (a₁ = a₂ 
↔ b₁ = b₂)
参数：a₁ == a₂；b₁ == b₂；a₁ = a₂ ↔ b₁ = b₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bool.eq_iff_iff`：∀ {a b : Bool}, a = b ↔ (a = true ↔ b = true)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma beq_eq_beq {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {a₁ a₂ : α}
    {b₁ b₂ : β} : (a₁ == a₂) = (b₁ == b₂) ↔ (a₁ = a₂ ↔ b₁ = b₂) := by rw [Bool.eq_iff_iff]; simp

@[ext]
/-
**beq_ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：beq_ext {α : Type*} (inst1 : BEq α) (inst2 : BEq α) (h : forall x y, @BEq.
beq _ inst1 x y = @BEq.beq _ inst2 x y) : inst1 = inst2
参数：inst1 : BEq α；inst2 : BEq α；h : forall x y, @BEq.beq _ inst1 x y = @BEq.beq _
 inst2 x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem beq_ext {α : Type*} (inst1 : BEq α) (inst2 : BEq α)
    (h : ∀ x y, @BEq.beq _ inst1 x y = @BEq.beq _ inst2 x y) :
    inst1 = inst2 := by
  have ⟨beq1⟩ := inst1
  congr
  funext x y
  exact h x y

set_option linter.overlappingInstances false in
/-
**lawful_beq_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lawful_beq_subsingleton {α : Type*} (inst1 : BEq α) (inst2 : BEq α) [@Lawf
ulBEq α inst1] [@LawfulBEq α inst2] : inst1 = inst2
参数：inst1 : BEq α；inst2 : BEq α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `beq_ext`：beq_ext {α : Type*} (inst1 : BEq α) (inst2 : BEq α) (h : forall
 x y, @BEq.beq _ inst1 x y = @BEq.beq _ inst2 x y) : inst1 = inst2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lawful_beq_subsingleton {α : Type*} (inst1 : BEq α) (inst2 : BEq α)
    [@LawfulBEq α inst1] [@LawfulBEq α inst2] :
    inst1 = inst2 := by
  ext
  simp
