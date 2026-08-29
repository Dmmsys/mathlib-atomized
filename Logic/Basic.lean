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

/--
theorem `eq_comm_eq` / 定理 `eq_comm_eq`

English:
theorem eq_comm_eq
  given: {α : Sort*} (a b : α)
  statement: (a = b) = (b = a)
  proof: by rw [@eq_comm _ a b]

中文:
定理 eq_comm_eq
  条件: {α : Sort*} (a b : α)
  结论: (a = b) = (b = a)
  证明: by rw [@eq_comm _ a b]

Depends on / 依赖: eq_comm
-/
theorem eq_comm_eq {α : Sort*} (a b : α) : (a = b) = (b = a) := by rw [@eq_comm _ a b]
/--
theorem `iff_comm_eq` / 定理 `iff_comm_eq`

English:
theorem iff_comm_eq
  given: (a b : Prop)
  statement: (a ↔ b) = (b ↔ a)
  proof: by rw [@iff_comm a b]

中文:
定理 iff_comm_eq
  条件: (a b : 命题)
  结论: (a ↔ b) = (b ↔ a)
  证明: by rw [@iff_comm a b]

Depends on / 依赖: iff_comm
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
withTraceNode `Meta.Tactic.simp (fun _ => return m!"commuting equality: {e}") simp symmExpr
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
      ``and_congr_left_iff, ``and_congr_right_iff, ``iff_def, ``iff_def',
      ``iff_iff_implies_and_implies, ``Bool.coe_iff_coe] do
withTraceNode `Meta.Tactic.simp (fun _ => return m!"commuting iff: {e}") simp symmExpr
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

/--
Definition of `hidden` / `hidden` 的定义

English:
abbreviation hidden
  signature: {α : Sort*} {a : α}
  body: a

中文:
缩写 hidden
  签名: {α : Sort*} {a : α}
  定义体: a
-/
abbrev hidden {α : Sort*} {a : α} := a

variable {α : Sort*}

instance (priority := 10) decidableEq_of_subsingleton [Subsingleton α] : DecidableEq α :=
  fun a b => isTrue (Subsingleton.elim a b)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: α] (p
  body: ⟨fun ⟨x, _⟩ ⟨y, _⟩ => by cases Subsingleton.elim x y; rfl⟩

中文:
实例 [Subsingleton
  签名: α] (p
  定义体: ⟨fun ⟨x, _⟩ ⟨y, _⟩ => by cases Subsingleton.elim x y; rfl⟩
-/
instance [Subsingleton α] (p : α -> Prop) : Subsingleton (Subtype p) :=
  ⟨fun ⟨x, _⟩ ⟨y, _⟩ => by cases Subsingleton.elim x y; rfl⟩

/--
theorem `congr_heq` / 定理 `congr_heq`

English:
theorem congr_heq
  statement: {α β γ : Sort _} {f : α -> γ} {g : β -> γ} {x : α} {y : β}
  proof: by
  cases h₂; cases h₁; rfl

中文:
定理 congr_heq
  结论: {α β γ : Sort _} {f : α -> γ} {g : β -> γ} {x : α} {y : β}
  证明: by
  cases h₂; cases h₁; rfl
-/
theorem congr_heq {α β γ : Sort _} {f : α -> γ} {g : β -> γ} {x : α} {y : β}
    (h₁ : f ≍ g) (h₂ : x ≍ y) : f x = g y := by
  cases h₂; cases h₁; rfl

/--
theorem `congr_arg_heq` / 定理 `congr_arg_heq`

English:
theorem congr_arg_heq
  given: {β : α -> Sort*} (f : forall a, β a)

中文:
定理 congr_arg_heq
  条件: {β : α -> Sort*} (f : 对任意 a, β a)
-/
theorem congr_arg_heq {β : α -> Sort*} (f : forall a, β a) :
    forall {a₁ a₂ : α}, a₁ = a₂ -> f a₁ ≍ f a₂
  | _, _, rfl => HEq.rfl

/--
theorem `dcongr_heq.` / 定理 `dcongr_heq.`

English:
theorem dcongr_heq.{u,
  statement: v}
  proof: by
  cases hargs
  cases funext fun v => ht v v .rfl
  cases hf rfl .rfl
  rfl

中文:
定理 dcongr_heq.{u,
  结论: v}
  证明: by
  cases hargs
  cases funext fun v => ht v v .rfl
  cases hf rfl .rfl
  rfl
-/
theorem dcongr_heq.{u, v}
    {α₁ α₂ : Sort u}
    {β₁ : α₁ -> Sort v} {β₂ : α₂ -> Sort v}
    {f₁ : forall a, β₁ a} {f₂ : forall a, β₂ a}
    {a₁ : α₁} {a₂ : α₂}
    (hargs : a₁ ≍ a₂)
    (ht : forall t₁ t₂, t₁ ≍ t₂ -> β₁ t₁ = β₂ t₂)
    (hf : α₁ = α₂ -> β₁ ≍ β₂ -> f₁ ≍ f₂) :
    f₁ a₁ ≍ f₂ a₂ := by
  cases hargs
  cases funext fun v => ht v v .rfl
  cases hf rfl .rfl
  rfl

/--
theorem `eq_iff_eq_cancel_left` / 定理 `eq_iff_eq_cancel_left`

English:
theorem eq_iff_eq_cancel_left
  given: {b c : α}
  statement: (forall {a}, a = b ↔ a = c) ↔ b = c
  proof: ⟨fun h => by rw [← h], fun h a => by rw [h]⟩

中文:
定理 eq_iff_eq_cancel_left
  条件: {b c : α}
  结论: (对任意 {a}, a = b ↔ a = c) ↔ b = c
  证明: ⟨fun h => by rw [← h], fun h a => by rw [h]⟩
-/
@[simp] theorem eq_iff_eq_cancel_left {b c : α} : (forall {a}, a = b ↔ a = c) ↔ b = c :=
  ⟨fun h => by rw [← h], fun h a => by rw [h]⟩

/--
theorem `eq_iff_eq_cancel_right` / 定理 `eq_iff_eq_cancel_right`

English:
theorem eq_iff_eq_cancel_right
  given: {a b : α}
  statement: (forall {c}, a = c ↔ b = c) ↔ a = b
  proof: ⟨fun h => by rw [h], fun h a => by rw [h]⟩

中文:
定理 eq_iff_eq_cancel_right
  条件: {a b : α}
  结论: (对任意 {c}, a = c ↔ b = c) ↔ a = b
  证明: ⟨fun h => by rw [h], fun h a => by rw [h]⟩
-/
@[simp] theorem eq_iff_eq_cancel_right {a b : α} : (forall {c}, a = c ↔ b = c) ↔ a = b :=
  ⟨fun h => by rw [h], fun h a => by rw [h]⟩

/--
lemma `ne_and_eq_iff_right` / 引理 `ne_and_eq_iff_right`

English:
lemma ne_and_eq_iff_right
  given: {a b c : α} (h : b != c)
  statement: a != b ∧ a = c ↔ a = c
  proof: and_iff_right_of_imp (fun h2 => h2.symm ▸ h.symm)

中文:
引理 ne_and_eq_iff_right
  条件: {a b c : α} (h : b != c)
  结论: a != b ∧ a = c ↔ a = c
  证明: and_iff_right_of_imp (fun h2 => h2.symm ▸ h.symm)

Depends on / 依赖: and_iff_right_of_imp, h.symm, h2.symm
-/
lemma ne_and_eq_iff_right {a b c : α} (h : b != c) : a != b ∧ a = c ↔ a = c :=
  and_iff_right_of_imp (fun h2 => h2.symm ▸ h.symm)

/--
Definition of `Fact` / `Fact` 的定义

English:
class Fact
  parameters: (p : Prop)
  axioms and operations (1):
    - out : p

中文:
类 Fact
  参数: (p : 命题)
  公理与运算 (1 个):
    - out : p
-/
class Fact (p : Prop) : Prop where

/--
theorem `Fact.elim` / 定理 `Fact.elim`

English:
theorem Fact.elim
  given: {p : Prop} (h : Fact p)
  statement: p
  proof: h.1

中文:
定理 Fact.elim
  条件: {p : 命题} (h : Fact p)
  结论: p
  证明: h.1
-/
theorem Fact.elim {p : Prop} (h : Fact p) : p := h.1
/--
theorem `fact_iff` / 定理 `fact_iff`

English:
theorem fact_iff
  given: {p : Prop}
  statement: Fact p ↔ p
  proof: ⟨fun h => h.1, fun h => ⟨h⟩⟩

中文:
定理 fact_iff
  条件: {p : 命题}
  结论: Fact p ↔ p
  证明: ⟨fun h => h.1, fun h => ⟨h⟩⟩
-/
theorem fact_iff {p : Prop} : Fact p ↔ p := ⟨fun h => h.1, fun h => ⟨h⟩⟩

instance {p : Prop} [Decidable p] : Decidable (Fact p) :=
  decidable_of_iff _ fact_iff.symm

/--
Definition of `Function.swap₂` / `Function.swap₂` 的定义

English:
abbreviation Function.swap₂
  signature: {ι₁ ι₂ : Sort*} {κ₁ : ι₁ -> Sort*} {κ₂ : ι₂ -> Sort*}
  body: f i₁ j₁ i₂ j₂

中文:
缩写 Function.swap₂
  签名: {ι₁ ι₂ : Sort*} {κ₁ : ι₁ -> Sort*} {κ₂ : ι₂ -> Sort*}
  定义体: f i₁ j₁ i₂ j₂
-/
abbrev Function.swap₂ {ι₁ ι₂ : Sort*} {κ₁ : ι₁ -> Sort*} {κ₂ : ι₂ -> Sort*}
    {φ : forall i₁, κ₁ i₁ -> forall i₂, κ₂ i₂ -> Sort*} (f : forall i₁ j₁ i₂ j₂, φ i₁ j₁ i₂ j₂)
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

/--
theorem `Function.mt` / 定理 `Function.mt`

English:
theorem Function.mt
  given: {a b : Prop}
  statement: (a -> b) -> ¬b -> ¬a
  proof: mt

中文:
定理 Function.mt
  条件: {a b : 命题}
  结论: (a -> b) -> ¬b -> ¬a
  证明: mt
-/
protected theorem Function.mt {a b : Prop} : (a -> b) -> ¬b -> ¬a := mt

/-! ### Declarations about `not` -/

alias dec_em := Decidable.em

set_option linter.unusedDecidableInType false in
/--
theorem `dec_em'` / 定理 `dec_em'`

English:
theorem dec_em'
  given: (p : Prop) [Decidable p]
  statement: ¬p ∨ p
  proof: (dec_em p).symm

alias em := Classical.em

中文:
定理 dec_em'
  条件: (p : 命题) [Decidable p]
  结论: ¬p ∨ p
  证明: (dec_em p).symm

alias em := Classical.em

Depends on / 依赖: dec_em
-/
theorem dec_em' (p : Prop) [Decidable p] : ¬p ∨ p := (dec_em p).symm

alias em := Classical.em

/--
theorem `em'` / 定理 `em'`

English:
theorem em'
  given: (p : Prop)
  statement: ¬p ∨ p
  proof: (em p).symm

中文:
定理 em'
  条件: (p : 命题)
  结论: ¬p ∨ p
  证明: (em p).symm
-/
theorem em' (p : Prop) : ¬p ∨ p := (em p).symm

/--
theorem `or_not` / 定理 `or_not`

English:
theorem or_not
  given: {p : Prop}
  statement: p ∨ ¬p
  proof: em _

中文:
定理 or_not
  条件: {p : 命题}
  结论: p ∨ ¬p
  证明: em _
-/
theorem or_not {p : Prop} : p ∨ ¬p := em _

/--
theorem `Decidable.eq_or_ne` / 定理 `Decidable.eq_or_ne`

English:
theorem Decidable.eq_or_ne
  given: {α : Sort*} (x y : α) [Decidable (x = y)]
  statement: x = y ∨ x != y
  proof: dec_em x = y

中文:
定理 Decidable.eq_or_ne
  条件: {α : Sort*} (x y : α) [Decidable (x = y)]
  结论: x = y ∨ x != y
  证明: dec_em x = y

Depends on / 依赖: dec_em
-/
theorem Decidable.eq_or_ne {α : Sort*} (x y : α) [Decidable (x = y)] : x = y ∨ x != y :=
dec_em x = y

/--
theorem `Decidable.ne_or_eq` / 定理 `Decidable.ne_or_eq`

English:
theorem Decidable.ne_or_eq
  given: {α : Sort*} (x y : α) [Decidable (x = y)]
  statement: x != y ∨ x = y
  proof: dec_em' x = y

中文:
定理 Decidable.ne_or_eq
  条件: {α : Sort*} (x y : α) [Decidable (x = y)]
  结论: x != y ∨ x = y
  证明: dec_em' x = y

Depends on / 依赖: dec_em
-/
theorem Decidable.ne_or_eq {α : Sort*} (x y : α) [Decidable (x = y)] : x != y ∨ x = y :=
dec_em' x = y

/--
theorem `eq_or_ne` / 定理 `eq_or_ne`

English:
theorem eq_or_ne
  given: {α : Sort*} (x y : α)
  statement: x = y ∨ x != y
  proof: em x = y

中文:
定理 eq_or_ne
  条件: {α : Sort*} (x y : α)
  结论: x = y ∨ x != y
  证明: em x = y
-/
theorem eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y := em x = y

/--
theorem `ne_or_eq` / 定理 `ne_or_eq`

English:
theorem ne_or_eq
  given: {α : Sort*} (x y : α)
  statement: x != y ∨ x = y
  proof: em' x = y

中文:
定理 ne_or_eq
  条件: {α : Sort*} (x y : α)
  结论: x != y ∨ x = y
  证明: em' x = y
-/
theorem ne_or_eq {α : Sort*} (x y : α) : x != y ∨ x = y := em' x = y

/--
theorem `by_contradiction` / 定理 `by_contradiction`

English:
theorem by_contradiction
  given: {p : Prop}
  statement: (¬p -> False) -> p
  proof: open scoped Classical in Decidable.byContradiction

中文:
定理 by_contradiction
  条件: {p : 命题}
  结论: (¬p -> False) -> p
  证明: open scoped Classical in Decidable.byContradiction

Depends on / 依赖: Classical, Decidable, Decidable.byContradiction, byContradiction, scoped
-/
theorem by_contradiction {p : Prop} : (¬p -> False) -> p :=
  open scoped Classical in Decidable.byContradiction

/--
theorem `by_cases` / 定理 `by_cases`

English:
theorem by_cases
  given: {p q : Prop} (hpq : p -> q) (hnpq : ¬p -> q)
  statement: q
  proof: open scoped Classical in if hp : p then hpq hp else hnpq hp

alias by_contra := by_contradiction

library_note «decidable namespace» /--
In most of mathlib, we use the law of excluded middle (LEM) and the axiom of choice (AC) freely.
The `Decidable` namespace contains versions of lemmas from the roo

中文:
定理 by_cases
  条件: {p q : 命题} (hpq : p -> q) (hnpq : ¬p -> q)
  结论: q
  证明: open scoped Classical in if hp : p then hpq hp else hnpq hp

alias by_contra := by_contradiction

library_note «decidable namespace» /--
In most of mathlib, we use the law of excluded middle (LEM) and the axiom of choice (AC) freely.
The `Decidable` namespace contains versions of lemmas from the roo

Depends on / 依赖: Classical, scoped
-/
theorem by_cases {p q : Prop} (hpq : p -> q) (hnpq : ¬p -> q) : q :=
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

/--
theorem `of_not_not` / 定理 `of_not_not`

English:
theorem of_not_not
  given: {a : Prop}
  statement: ¬¬a -> a
  proof: by_contra

中文:
定理 of_not_not
  条件: {a : 命题}
  结论: ¬¬a -> a
  证明: by_contra
-/
theorem of_not_not {a : Prop} : ¬¬a -> a := by_contra

/--
theorem `not_ne_iff` / 定理 `not_ne_iff`

English:
theorem not_ne_iff
  given: {α : Sort*} {a b : α}
  statement: ¬a != b ↔ a = b
  proof: not_not

中文:
定理 not_ne_iff
  条件: {α : Sort*} {a b : α}
  结论: ¬a != b ↔ a = b
  证明: not_not

Depends on / 依赖: not_not
-/
theorem not_ne_iff {α : Sort*} {a b : α} : ¬a != b ↔ a = b := not_not

/--
theorem `of_not_imp` / 定理 `of_not_imp`

English:
theorem of_not_imp
  statement: ¬(a -> b) -> a
  proof: open scoped Classical in Decidable.of_not_imp

alias Not.decidable_imp_symm := Decidable.not_imp_symm

中文:
定理 of_not_imp
  结论: ¬(a -> b) -> a
  证明: open scoped Classical in Decidable.of_not_imp

alias Not.decidable_imp_symm := Decidable.not_imp_symm

Depends on / 依赖: Classical, Decidable, Decidable.of_not_imp, of_not_imp, scoped
-/
theorem of_not_imp : ¬(a -> b) -> a := open scoped Classical in Decidable.of_not_imp

alias Not.decidable_imp_symm := Decidable.not_imp_symm

/--
theorem `Not.imp_symm` / 定理 `Not.imp_symm`

English:
theorem Not.imp_symm
  statement: (¬a -> b) -> ¬b -> a
  proof: open scoped Classical in Not.decidable_imp_symm

中文:
定理 Not.imp_symm
  结论: (¬a -> b) -> ¬b -> a
  证明: open scoped Classical in Not.decidable_imp_symm

Depends on / 依赖: Classical, Not.decidable_imp_symm, decidable_imp_symm, scoped
-/
theorem Not.imp_symm : (¬a -> b) -> ¬b -> a := open scoped Classical in Not.decidable_imp_symm

/--
theorem `not_imp_comm` / 定理 `not_imp_comm`

English:
theorem not_imp_comm
  statement: ¬a -> b ↔ ¬b -> a
  proof: open scoped Classical in Decidable.not_imp_comm

中文:
定理 not_imp_comm
  结论: ¬a -> b ↔ ¬b -> a
  证明: open scoped Classical in Decidable.not_imp_comm

Depends on / 依赖: Classical, Decidable, Decidable.not_imp_comm, not_imp_comm, scoped
-/
theorem not_imp_comm : ¬a -> b ↔ ¬b -> a := open scoped Classical in Decidable.not_imp_comm

/--
theorem `not_imp_self` / 定理 `not_imp_self`

English:
theorem not_imp_self
  statement: ¬a -> a ↔ a
  proof: open scoped Classical in Decidable.not_imp_self

中文:
定理 not_imp_self
  结论: ¬a -> a ↔ a
  证明: open scoped Classical in Decidable.not_imp_self
-/
@[simp] theorem not_imp_self : ¬a -> a ↔ a := open scoped Classical in Decidable.not_imp_self

/--
theorem `Imp.swap` / 定理 `Imp.swap`

English:
theorem Imp.swap
  given: {a b : Sort*} {c : Prop}
  statement: a -> b -> c ↔ b -> a -> c
  proof: ⟨fun h x y => h y x, fun h x y => h y x⟩

alias Iff.not := not_congr

中文:
定理 Imp.swap
  条件: {a b : Sort*} {c : 命题}
  结论: a -> b -> c ↔ b -> a -> c
  证明: ⟨fun h x y => h y x, fun h x y => h y x⟩

alias Iff.not := not_congr
-/
theorem Imp.swap {a b : Sort*} {c : Prop} : a -> b -> c ↔ b -> a -> c :=
  ⟨fun h x y => h y x, fun h x y => h y x⟩

alias Iff.not := not_congr

/--
theorem `Iff.not_left` / 定理 `Iff.not_left`

English:
theorem Iff.not_left
  given: (h : a ↔ ¬b)
  statement: ¬a ↔ b
  proof: h.not.trans not_not

中文:
定理 Iff.not_left
  条件: (h : a ↔ ¬b)
  结论: ¬a ↔ b
  证明: h.not.trans not_not

Depends on / 依赖: h.not.trans, not_not
-/
theorem Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b := h.not.trans not_not

/--
theorem `Iff.not_right` / 定理 `Iff.not_right`

English:
theorem Iff.not_right
  given: (h : ¬a ↔ b)
  statement: a ↔ ¬b
  proof: not_not.symm.trans h.not

中文:
定理 Iff.not_right
  条件: (h : ¬a ↔ b)
  结论: a ↔ ¬b
  证明: not_not.symm.trans h.not

Depends on / 依赖: h.not, not_not, not_not.symm.trans
-/
theorem Iff.not_right (h : ¬a ↔ b) : a ↔ ¬b := not_not.symm.trans h.not

/--
lemma `Iff.ne` / 引理 `Iff.ne`

English:
lemma Iff.ne
  given: {α β : Sort*} {a b : α} {c d : β}
  statement: (a = b ↔ c = d) -> (a != b ↔ c != d)
  proof: Iff.not

中文:
引理 Iff.ne
  条件: {α β : Sort*} {a b : α} {c d : β}
  结论: (a = b ↔ c = d) -> (a != b ↔ c != d)
  证明: Iff.not
-/
protected lemma Iff.ne {α β : Sort*} {a b : α} {c d : β} : (a = b ↔ c = d) -> (a != b ↔ c != d) :=
  Iff.not

/--
lemma `Iff.ne_left` / 引理 `Iff.ne_left`

English:
lemma Iff.ne_left
  given: {α β : Sort*} {a b : α} {c d : β}
  statement: (a = b ↔ c != d) -> (a != b ↔ c = d)
  proof: Iff.not_left

中文:
引理 Iff.ne_left
  条件: {α β : Sort*} {a b : α} {c d : β}
  结论: (a = b ↔ c != d) -> (a != b ↔ c = d)
  证明: Iff.not_left

Depends on / 依赖: Iff.not_left, not_left
-/
lemma Iff.ne_left {α β : Sort*} {a b : α} {c d : β} : (a = b ↔ c != d) -> (a != b ↔ c = d) :=
  Iff.not_left

/--
lemma `Iff.ne_right` / 引理 `Iff.ne_right`

English:
lemma Iff.ne_right
  given: {α β : Sort*} {a b : α} {c d : β}
  statement: (a != b ↔ c = d) -> (a = b ↔ c != d)
  proof: Iff.not_right

中文:
引理 Iff.ne_right
  条件: {α β : Sort*} {a b : α} {c d : β}
  结论: (a != b ↔ c = d) -> (a = b ↔ c != d)
  证明: Iff.not_right

Depends on / 依赖: Iff.not_right, not_right
-/
lemma Iff.ne_right {α β : Sort*} {a b : α} {c d : β} : (a != b ↔ c = d) -> (a = b ↔ c != d) :=
  Iff.not_right

/-! ### Declarations about `Xor` -/

/--
Definition of `Xor` / `Xor` 的定义

English:
definition Xor
  signature: (a b : Prop)
  body: (a ∧ ¬b) ∨ (b ∧ ¬a)

@[deprecated (since := "2026-04-27")] alias Xor' := Xor

中文:
定义 Xor
  签名: (a b : 命题)
  定义体: (a ∧ ¬b) ∨ (b ∧ ¬a)

@[deprecated (since := "2026-04-27")] alias Xor' := Xor
-/
def Xor (a b : Prop) := (a ∧ ¬b) ∨ (b ∧ ¬a)

@[deprecated (since := "2026-04-27")] alias Xor' := Xor

/--
theorem `xor_def` / 定理 `xor_def`

English:
theorem xor_def
  given: {a b : Prop}
  statement: Xor a b ↔ (a ∧ ¬b) ∨ (b ∧ ¬a)
  proof: Iff.rfl

中文:
定理 xor_def
  条件: {a b : 命题}
  结论: Xor a b ↔ (a ∧ ¬b) ∨ (b ∧ ¬a)
  证明: Iff.rfl
-/
@[grind =] theorem xor_def {a b : Prop} : Xor a b ↔ (a ∧ ¬b) ∨ (b ∧ ¬a) := Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Decidable
  signature: a] [Decidable b] : Decidable (Xor a b)
  body: inferInstanceAs (Decidable (Or ..))

中文:
实例 [Decidable
  签名: a] [Decidable b] : Decidable (Xor a b)
  定义体: inferInstanceAs (Decidable (Or ..))

Depends on / 依赖: Decidable
-/
instance [Decidable a] [Decidable b] : Decidable (Xor a b) := inferInstanceAs (Decidable (Or ..))

/--
theorem `xor_true` / 定理 `xor_true`

English:
theorem xor_true
  statement: Xor True = Not
  proof: by grind

中文:
定理 xor_true
  结论: Xor True = Not
  证明: by grind
-/
@[simp] theorem xor_true : Xor True = Not := by grind

/--
theorem `xor_false` / 定理 `xor_false`

English:
theorem xor_false
  statement: Xor False = id
  proof: by grind

中文:
定理 xor_false
  结论: Xor False = id
  证明: by grind
-/
@[simp] theorem xor_false : Xor False = id := by grind

/--
theorem `xor_comm` / 定理 `xor_comm`

English:
theorem xor_comm
  given: (a b : Prop)
  statement: Xor a b = Xor b a
  proof: by grind

中文:
定理 xor_comm
  条件: (a b : 命题)
  结论: Xor a b = Xor b a
  证明: by grind
-/
theorem xor_comm (a b : Prop) : Xor a b = Xor b a := by grind

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.Commutative Xor
  body: ⟨xor_comm⟩

中文:
实例 :
  签名: Std.Commutative Xor
  定义体: ⟨xor_comm⟩

Depends on / 依赖: xor_comm
-/
instance : Std.Commutative Xor := ⟨xor_comm⟩

/--
theorem `xor_self` / 定理 `xor_self`

English:
theorem xor_self
  given: (a : Prop)
  statement: Xor a a = False
  proof: by grind

中文:
定理 xor_self
  条件: (a : 命题)
  结论: Xor a a = False
  证明: by grind
-/
@[simp] theorem xor_self (a : Prop) : Xor a a = False := by grind

/--
theorem `xor_not_left` / 定理 `xor_not_left`

English:
theorem xor_not_left
  statement: Xor (¬a) b ↔ (a ↔ b)
  proof: by grind

中文:
定理 xor_not_left
  结论: Xor (¬a) b ↔ (a ↔ b)
  证明: by grind
-/
@[simp] theorem xor_not_left : Xor (¬a) b ↔ (a ↔ b) := by grind

/--
theorem `xor_not_right` / 定理 `xor_not_right`

English:
theorem xor_not_right
  statement: Xor a (¬b) ↔ (a ↔ b)
  proof: by grind

中文:
定理 xor_not_right
  结论: Xor a (¬b) ↔ (a ↔ b)
  证明: by grind
-/
@[simp] theorem xor_not_right : Xor a (¬b) ↔ (a ↔ b) := by grind

/--
theorem `xor_not_not` / 定理 `xor_not_not`

English:
theorem xor_not_not
  statement: Xor (¬a) (¬b) ↔ Xor a b
  proof: by grind

中文:
定理 xor_not_not
  结论: Xor (¬a) (¬b) ↔ Xor a b
  证明: by grind
-/
theorem xor_not_not : Xor (¬a) (¬b) ↔ Xor a b := by grind

/--
theorem `Xor.or` / 定理 `Xor.or`

English:
theorem Xor.or
  given: (h : Xor a b)
  statement: a ∨ b
  proof: by grind

@[deprecated (since := "2026-04-27")]
protected alias Xor'.or := Xor.or

中文:
定理 Xor.or
  条件: (h : Xor a b)
  结论: a ∨ b
  证明: by grind

@[deprecated (since := "2026-04-27")]
protected alias Xor'.or := Xor.or
-/
protected theorem Xor.or (h : Xor a b) : a ∨ b := by grind

@[deprecated (since := "2026-04-27")]
protected alias Xor'.or := Xor.or

/-! ### Declarations about `and` -/

alias Iff.and := and_congr
alias ⟨And.rotate, _⟩ := and_rotate

/--
theorem `and_symm_right` / 定理 `and_symm_right`

English:
theorem and_symm_right
  given: {α : Sort*} (a b : α) (p : Prop)
  statement: p ∧ a = b ↔ p ∧ b = a
  proof: by simp [eq_comm]

中文:
定理 and_symm_right
  条件: {α : Sort*} (a b : α) (p : 命题)
  结论: p ∧ a = b ↔ p ∧ b = a
  证明: by simp [eq_comm]

Depends on / 依赖: eq_comm
-/
theorem and_symm_right {α : Sort*} (a b : α) (p : Prop) : p ∧ a = b ↔ p ∧ b = a := by simp [eq_comm]
/--
theorem `and_symm_left` / 定理 `and_symm_left`

English:
theorem and_symm_left
  given: {α : Sort*} (a b : α) (p : Prop)
  statement: a = b ∧ p ↔ b = a ∧ p
  proof: by simp [eq_comm]

中文:
定理 and_symm_left
  条件: {α : Sort*} (a b : α) (p : 命题)
  结论: a = b ∧ p ↔ b = a ∧ p
  证明: by simp [eq_comm]

Depends on / 依赖: eq_comm
-/
theorem and_symm_left {α : Sort*} (a b : α) (p : Prop) : a = b ∧ p ↔ b = a ∧ p := by simp [eq_comm]

/-! ### Declarations about `or` -/

alias Iff.or := or_congr
alias ⟨Or.rotate, _⟩ := or_rotate

/--
theorem `Or.elim3` / 定理 `Or.elim3`

English:
theorem Or.elim3
  given: {c d : Prop} (h : a ∨ b ∨ c) (ha : a -> d) (hb : b -> d) (hc : c -> d)
  statement: d
  proof: Or.elim h ha fun h₂ => Or.elim h₂ hb hc

中文:
定理 Or.elim3
  条件: {c d : 命题} (h : a ∨ b ∨ c) (ha : a -> d) (hb : b -> d) (hc : c -> d)
  结论: d
  证明: Or.elim h ha fun h₂ => Or.elim h₂ hb hc

Depends on / 依赖: Or.elim
-/
theorem Or.elim3 {c d : Prop} (h : a ∨ b ∨ c) (ha : a -> d) (hb : b -> d) (hc : c -> d) : d :=
  Or.elim h ha fun h₂ => Or.elim h₂ hb hc

/--
theorem `Or.imp3` / 定理 `Or.imp3`

English:
theorem Or.imp3
  given: {d e c f : Prop} (had : a -> d) (hbe : b -> e) (hcf : c -> f)
  proof: Or.imp had Or.imp hbe hcf

中文:
定理 Or.imp3
  条件: {d e c f : 命题} (had : a -> d) (hbe : b -> e) (hcf : c -> f)
  证明: Or.imp had Or.imp hbe hcf

Depends on / 依赖: Or.imp
-/
theorem Or.imp3 {d e c f : Prop} (had : a -> d) (hbe : b -> e) (hcf : c -> f) :
    a ∨ b ∨ c -> d ∨ e ∨ f :=
Or.imp had Or.imp hbe hcf

export Classical (or_iff_not_imp_left or_iff_not_imp_right)

/--
theorem `not_or_of_imp` / 定理 `not_or_of_imp`

English:
theorem not_or_of_imp
  statement: (a -> b) -> ¬a ∨ b
  proof: open scoped Classical in Decidable.not_or_of_imp

中文:
定理 not_or_of_imp
  结论: (a -> b) -> ¬a ∨ b
  证明: open scoped Classical in Decidable.not_or_of_imp

Depends on / 依赖: Classical, Decidable, Decidable.not_or_of_imp, not_or_of_imp, scoped
-/
theorem not_or_of_imp : (a -> b) -> ¬a ∨ b := open scoped Classical in Decidable.not_or_of_imp

-- See Note [decidable namespace]
/--
theorem `Decidable.or_not_of_imp` / 定理 `Decidable.or_not_of_imp`

English:
theorem Decidable.or_not_of_imp
  given: [Decidable a] (h : a -> b)
  statement: b ∨ ¬a
  proof: dite _ (Or.inl ∘ h) Or.inr

中文:
定理 Decidable.or_not_of_imp
  条件: [Decidable a] (h : a -> b)
  结论: b ∨ ¬a
  证明: dite _ (Or.inl ∘ h) Or.inr
-/
protected theorem Decidable.or_not_of_imp [Decidable a] (h : a -> b) : b ∨ ¬a :=
  dite _ (Or.inl ∘ h) Or.inr

/--
theorem `or_not_of_imp` / 定理 `or_not_of_imp`

English:
theorem or_not_of_imp
  statement: (a -> b) -> b ∨ ¬a
  proof: open scoped Classical in Decidable.or_not_of_imp

中文:
定理 or_not_of_imp
  结论: (a -> b) -> b ∨ ¬a
  证明: open scoped Classical in Decidable.or_not_of_imp

Depends on / 依赖: Classical, Decidable, Decidable.or_not_of_imp, or_not_of_imp, scoped
-/
theorem or_not_of_imp : (a -> b) -> b ∨ ¬a := open scoped Classical in Decidable.or_not_of_imp

/--
theorem `imp_iff_not_or` / 定理 `imp_iff_not_or`

English:
theorem imp_iff_not_or
  statement: a -> b ↔ ¬a ∨ b
  proof: open scoped Classical in Decidable.imp_iff_not_or

中文:
定理 imp_iff_not_or
  结论: a -> b ↔ ¬a ∨ b
  证明: open scoped Classical in Decidable.imp_iff_not_or

Depends on / 依赖: Classical, Decidable, Decidable.imp_iff_not_or, imp_iff_not_or, scoped
-/
theorem imp_iff_not_or : a -> b ↔ ¬a ∨ b := open scoped Classical in Decidable.imp_iff_not_or

/--
theorem `imp_iff_or_not` / 定理 `imp_iff_or_not`

English:
theorem imp_iff_or_not
  given: {b a : Prop}
  statement: b -> a ↔ a ∨ ¬b
  proof: open scoped Classical in Decidable.imp_iff_or_not

中文:
定理 imp_iff_or_not
  条件: {b a : 命题}
  结论: b -> a ↔ a ∨ ¬b
  证明: open scoped Classical in Decidable.imp_iff_or_not

Depends on / 依赖: Classical, Decidable, Decidable.imp_iff_or_not, imp_iff_or_not, scoped
-/
theorem imp_iff_or_not {b a : Prop} : b -> a ↔ a ∨ ¬b :=
  open scoped Classical in Decidable.imp_iff_or_not

/--
theorem `not_imp_not` / 定理 `not_imp_not`

English:
theorem not_imp_not
  statement: ¬a -> ¬b ↔ b -> a
  proof: open scoped Classical in Decidable.not_imp_not

@[deprecated Classical.imp_and_neg_imp_iff (since := "2026-01-30")]

中文:
定理 not_imp_not
  结论: ¬a -> ¬b ↔ b -> a
  证明: open scoped Classical in Decidable.not_imp_not

@[deprecated Classical.imp_and_neg_imp_iff (since := "2026-01-30")]

Depends on / 依赖: Classical, Decidable, Decidable.not_imp_not, not_imp_not, scoped
-/
theorem not_imp_not : ¬a -> ¬b ↔ b -> a := open scoped Classical in Decidable.not_imp_not

@[deprecated Classical.imp_and_neg_imp_iff (since := "2026-01-30")]
/--
theorem `imp_and_neg_imp_iff` / 定理 `imp_and_neg_imp_iff`

English:
theorem imp_and_neg_imp_iff
  given: (p q : Prop)
  statement: (p -> q) ∧ (¬p -> q) ↔ q
  proof: Classical.imp_and_neg_imp_iff p

中文:
定理 imp_and_neg_imp_iff
  条件: (p q : 命题)
  结论: (p -> q) ∧ (¬p -> q) ↔ q
  证明: Classical.imp_and_neg_imp_iff p

Depends on / 依赖: Classical, Classical.imp_and_neg_imp_iff, imp_and_neg_imp_iff
-/
theorem imp_and_neg_imp_iff (p q : Prop) : (p -> q) ∧ (¬p -> q) ↔ q :=
  Classical.imp_and_neg_imp_iff p

/--
theorem `Function.mtr` / 定理 `Function.mtr`

English:
theorem Function.mtr
  statement: (¬a -> ¬b) -> b -> a
  proof: not_imp_not.mp

中文:
定理 Function.mtr
  结论: (¬a -> ¬b) -> b -> a
  证明: not_imp_not.mp
-/
protected theorem Function.mtr : (¬a -> ¬b) -> b -> a := not_imp_not.mp

/--
theorem `or_congr_left'` / 定理 `or_congr_left'`

English:
theorem or_congr_left'
  given: {c a b : Prop} (h : ¬c -> (a ↔ b))
  statement: a ∨ c ↔ b ∨ c
  proof: open scoped Classical in Decidable.or_congr_left' h

中文:
定理 or_congr_left'
  条件: {c a b : 命题} (h : ¬c -> (a ↔ b))
  结论: a ∨ c ↔ b ∨ c
  证明: open scoped Classical in Decidable.or_congr_left' h

Depends on / 依赖: Classical, Decidable, Decidable.or_congr_left, or_congr_left, scoped
-/
theorem or_congr_left' {c a b : Prop} (h : ¬c -> (a ↔ b)) : a ∨ c ↔ b ∨ c :=
  open scoped Classical in Decidable.or_congr_left' h

/--
theorem `or_congr_right'` / 定理 `or_congr_right'`

English:
theorem or_congr_right'
  given: {c : Prop} (h : ¬a -> (b ↔ c))
  statement: a ∨ b ↔ a ∨ c
  proof: open scoped Classical in Decidable.or_congr_right' h

中文:
定理 or_congr_right'
  条件: {c : 命题} (h : ¬a -> (b ↔ c))
  结论: a ∨ b ↔ a ∨ c
  证明: open scoped Classical in Decidable.or_congr_right' h

Depends on / 依赖: Classical, Decidable, Decidable.or_congr_right, or_congr_right, scoped
-/
theorem or_congr_right' {c : Prop} (h : ¬a -> (b ↔ c)) : a ∨ b ↔ a ∨ c :=
  open scoped Classical in Decidable.or_congr_right' h

/-! ### Declarations about distributivity -/

/-! Declarations about `iff` -/

alias Iff.iff := iff_congr

-- @[simp] -- FIXME simp ignores proof rewrites
/--
theorem `iff_mpr_iff_true_intro` / 定理 `iff_mpr_iff_true_intro`

English:
theorem iff_mpr_iff_true_intro
  given: {P : Prop} (h : P)
  statement: Iff.mpr (iff_true_intro h) True.intro = h
  proof: rfl

中文:
定理 iff_mpr_iff_true_intro
  条件: {P : 命题} (h : P)
  结论: Iff.mpr (iff_true_intro h) True.intro = h
  证明: rfl
-/
theorem iff_mpr_iff_true_intro {P : Prop} (h : P) : Iff.mpr (iff_true_intro h) True.intro = h := rfl

/--
theorem `imp_or` / 定理 `imp_or`

English:
theorem imp_or
  given: {a b c : Prop}
  statement: a -> b ∨ c ↔ (a -> b) ∨ (a -> c)
  proof: open scoped Classical in Decidable.imp_or

中文:
定理 imp_or
  条件: {a b c : 命题}
  结论: a -> b ∨ c ↔ (a -> b) ∨ (a -> c)
  证明: open scoped Classical in Decidable.imp_or

Depends on / 依赖: Classical, Decidable, Decidable.imp_or, imp_or, scoped
-/
theorem imp_or {a b c : Prop} : a -> b ∨ c ↔ (a -> b) ∨ (a -> c) :=
  open scoped Classical in Decidable.imp_or

/--
theorem `imp_or'` / 定理 `imp_or'`

English:
theorem imp_or'
  given: {a : Sort*} {b c : Prop}
  statement: a -> b ∨ c ↔ (a -> b) ∨ (a -> c)
  proof: open scoped Classical in Decidable.imp_or'

@[deprecated (since := "2026-01-30")] alias not_imp := Classical.not_imp

中文:
定理 imp_or'
  条件: {a : Sort*} {b c : 命题}
  结论: a -> b ∨ c ↔ (a -> b) ∨ (a -> c)
  证明: open scoped Classical in Decidable.imp_or'

@[deprecated (since := "2026-01-30")] alias not_imp := Classical.not_imp

Depends on / 依赖: Classical, Decidable, Decidable.imp_or, imp_or, scoped
-/
theorem imp_or' {a : Sort*} {b c : Prop} : a -> b ∨ c ↔ (a -> b) ∨ (a -> c) :=
  open scoped Classical in Decidable.imp_or'

@[deprecated (since := "2026-01-30")] alias not_imp := Classical.not_imp

/--
theorem `peirce` / 定理 `peirce`

English:
theorem peirce
  given: (a b : Prop)
  statement: ((a -> b) -> a) -> a
  proof: open scoped Classical in Decidable.peirce _ _

中文:
定理 peirce
  条件: (a b : 命题)
  结论: ((a -> b) -> a) -> a
  证明: open scoped Classical in Decidable.peirce _ _

Depends on / 依赖: Classical, Decidable, Decidable.peirce, peirce, scoped
-/
theorem peirce (a b : Prop) : ((a -> b) -> a) -> a := open scoped Classical in Decidable.peirce _ _

/--
theorem `not_iff_not` / 定理 `not_iff_not`

English:
theorem not_iff_not
  statement: (¬a ↔ ¬b) ↔ (a ↔ b)
  proof: open scoped Classical in Decidable.not_iff_not

中文:
定理 not_iff_not
  结论: (¬a ↔ ¬b) ↔ (a ↔ b)
  证明: open scoped Classical in Decidable.not_iff_not

Depends on / 依赖: Classical, Decidable, Decidable.not_iff_not, not_iff_not, scoped
-/
theorem not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b) := open scoped Classical in Decidable.not_iff_not

/--
theorem `not_iff_comm` / 定理 `not_iff_comm`

English:
theorem not_iff_comm
  statement: (¬a ↔ b) ↔ (¬b ↔ a)
  proof: open scoped Classical in Decidable.not_iff_comm

中文:
定理 not_iff_comm
  结论: (¬a ↔ b) ↔ (¬b ↔ a)
  证明: open scoped Classical in Decidable.not_iff_comm

Depends on / 依赖: Classical, Decidable, Decidable.not_iff_comm, not_iff_comm, scoped
-/
theorem not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a) := open scoped Classical in Decidable.not_iff_comm

/--
theorem `not_iff` / 定理 `not_iff`

English:
theorem not_iff
  statement: ¬(a ↔ b) ↔ (¬a ↔ b)
  proof: open scoped Classical in Decidable.not_iff

中文:
定理 not_iff
  结论: ¬(a ↔ b) ↔ (¬a ↔ b)
  证明: open scoped Classical in Decidable.not_iff

Depends on / 依赖: Classical, Decidable, Decidable.not_iff, not_iff, scoped
-/
theorem not_iff : ¬(a ↔ b) ↔ (¬a ↔ b) := open scoped Classical in Decidable.not_iff

/--
theorem `iff_not_comm` / 定理 `iff_not_comm`

English:
theorem iff_not_comm
  statement: (a ↔ ¬b) ↔ (b ↔ ¬a)
  proof: open scoped Classical in Decidable.iff_not_comm

中文:
定理 iff_not_comm
  结论: (a ↔ ¬b) ↔ (b ↔ ¬a)
  证明: open scoped Classical in Decidable.iff_not_comm

Depends on / 依赖: Classical, Decidable, Decidable.iff_not_comm, iff_not_comm, scoped
-/
theorem iff_not_comm : (a ↔ ¬b) ↔ (b ↔ ¬a) := open scoped Classical in Decidable.iff_not_comm

/--
theorem `iff_iff_and_or_not_and_not` / 定理 `iff_iff_and_or_not_and_not`

English:
theorem iff_iff_and_or_not_and_not
  statement: (a ↔ b) ↔ a ∧ b ∨ ¬a ∧ ¬b
  proof: open scoped Classical in Decidable.iff_iff_and_or_not_and_not

中文:
定理 iff_iff_and_or_not_and_not
  结论: (a ↔ b) ↔ a ∧ b ∨ ¬a ∧ ¬b
  证明: open scoped Classical in Decidable.iff_iff_and_or_not_and_not

Depends on / 依赖: Classical, Decidable, Decidable.iff_iff_and_or_not_and_not, iff_iff_and_or_not_and_not, scoped
-/
theorem iff_iff_and_or_not_and_not : (a ↔ b) ↔ a ∧ b ∨ ¬a ∧ ¬b :=
  open scoped Classical in Decidable.iff_iff_and_or_not_and_not

/--
theorem `iff_iff_not_or_and_or_not` / 定理 `iff_iff_not_or_and_or_not`

English:
theorem iff_iff_not_or_and_or_not
  statement: (a ↔ b) ↔ (¬a ∨ b) ∧ (a ∨ ¬b)
  proof: open scoped Classical in Decidable.iff_iff_not_or_and_or_not

中文:
定理 iff_iff_not_or_and_or_not
  结论: (a ↔ b) ↔ (¬a ∨ b) ∧ (a ∨ ¬b)
  证明: open scoped Classical in Decidable.iff_iff_not_or_and_or_not

Depends on / 依赖: Classical, Decidable, Decidable.iff_iff_not_or_and_or_not, iff_iff_not_or_and_or_not, scoped
-/
theorem iff_iff_not_or_and_or_not : (a ↔ b) ↔ (¬a ∨ b) ∧ (a ∨ ¬b) :=
  open scoped Classical in Decidable.iff_iff_not_or_and_or_not

/--
theorem `not_and_not_right` / 定理 `not_and_not_right`

English:
theorem not_and_not_right
  statement: ¬(a ∧ ¬b) ↔ a -> b
  proof: open scoped Classical in Decidable.not_and_not_right

中文:
定理 not_and_not_right
  结论: ¬(a ∧ ¬b) ↔ a -> b
  证明: open scoped Classical in Decidable.not_and_not_right

Depends on / 依赖: Classical, Decidable, Decidable.not_and_not_right, not_and_not_right, scoped
-/
theorem not_and_not_right : ¬(a ∧ ¬b) ↔ a -> b :=
  open scoped Classical in Decidable.not_and_not_right

/-! ### De Morgan's laws -/

/--
theorem `not_and_or` / 定理 `not_and_or`

English:
theorem not_and_or
  statement: ¬(a ∧ b) ↔ ¬a ∨ ¬b
  proof: open scoped Classical in Decidable.not_and_iff_not_or_not

中文:
定理 not_and_or
  结论: ¬(a ∧ b) ↔ ¬a ∨ ¬b
  证明: open scoped Classical in Decidable.not_and_iff_not_or_not

Depends on / 依赖: Classical, Decidable, Decidable.not_and_iff_not_or_not, not_and_iff_not_or_not, scoped
-/
theorem not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b := open scoped Classical in Decidable.not_and_iff_not_or_not

/--
theorem `or_iff_not_and_not` / 定理 `or_iff_not_and_not`

English:
theorem or_iff_not_and_not
  statement: a ∨ b ↔ ¬(¬a ∧ ¬b)
  proof: open scoped Classical in Decidable.or_iff_not_not_and_not

中文:
定理 or_iff_not_and_not
  结论: a ∨ b ↔ ¬(¬a ∧ ¬b)
  证明: open scoped Classical in Decidable.or_iff_not_not_and_not

Depends on / 依赖: Classical, Decidable, Decidable.or_iff_not_not_and_not, or_iff_not_not_and_not, scoped
-/
theorem or_iff_not_and_not : a ∨ b ↔ ¬(¬a ∧ ¬b) :=
  open scoped Classical in Decidable.or_iff_not_not_and_not

/--
theorem `and_iff_not_or_not` / 定理 `and_iff_not_or_not`

English:
theorem and_iff_not_or_not
  statement: a ∧ b ↔ ¬(¬a ∨ ¬b)
  proof: open scoped Classical in Decidable.and_iff_not_not_or_not

中文:
定理 and_iff_not_or_not
  结论: a ∧ b ↔ ¬(¬a ∨ ¬b)
  证明: open scoped Classical in Decidable.and_iff_not_not_or_not

Depends on / 依赖: Classical, Decidable, Decidable.and_iff_not_not_or_not, and_iff_not_not_or_not, scoped
-/
theorem and_iff_not_or_not : a ∧ b ↔ ¬(¬a ∨ ¬b) :=
  open scoped Classical in Decidable.and_iff_not_not_or_not

/--
theorem `not_xor` / 定理 `not_xor`

English:
theorem not_xor
  given: (P Q : Prop)
  statement: ¬Xor P Q ↔ (P ↔ Q)
  proof: by
  simp only [not_and, Xor, not_or, not_not, ← iff_iff_implies_and_implies]

中文:
定理 not_xor
  条件: (P Q : 命题)
  结论: ¬Xor P Q ↔ (P ↔ Q)
  证明: by
  simp only [not_and, Xor, not_or, not_not, ← iff_iff_implies_and_implies]
-/
@[simp] theorem not_xor (P Q : Prop) : ¬Xor P Q ↔ (P ↔ Q) := by
  simp only [not_and, Xor, not_or, not_not, ← iff_iff_implies_and_implies]

/--
theorem `xor_iff_not_iff` / 定理 `xor_iff_not_iff`

English:
theorem xor_iff_not_iff
  given: (P Q : Prop)
  statement: Xor P Q ↔ ¬(P ↔ Q)
  proof: (not_xor P Q).not_right

中文:
定理 xor_iff_not_iff
  条件: (P Q : 命题)
  结论: Xor P Q ↔ ¬(P ↔ Q)
  证明: (not_xor P Q).not_right

Depends on / 依赖: not_right, not_xor
-/
theorem xor_iff_not_iff (P Q : Prop) : Xor P Q ↔ ¬(P ↔ Q) := (not_xor P Q).not_right

/--
theorem `xor_iff_iff_not` / 定理 `xor_iff_iff_not`

English:
theorem xor_iff_iff_not
  statement: Xor a b ↔ (a ↔ ¬b)
  proof: by simp only [← @xor_not_right a, not_not]

中文:
定理 xor_iff_iff_not
  结论: Xor a b ↔ (a ↔ ¬b)
  证明: by simp only [← @xor_not_right a, not_not]

Depends on / 依赖: not_not, xor_not_right
-/
theorem xor_iff_iff_not : Xor a b ↔ (a ↔ ¬b) := by simp only [← @xor_not_right a, not_not]

/--
theorem `xor_iff_not_iff'` / 定理 `xor_iff_not_iff'`

English:
theorem xor_iff_not_iff'
  statement: Xor a b ↔ (¬a ↔ b)
  proof: by simp only [← @xor_not_left _ b, not_not]

中文:
定理 xor_iff_not_iff'
  结论: Xor a b ↔ (¬a ↔ b)
  证明: by simp only [← @xor_not_left _ b, not_not]

Depends on / 依赖: not_not, xor_not_left
-/
theorem xor_iff_not_iff' : Xor a b ↔ (¬a ↔ b) := by simp only [← @xor_not_left _ b, not_not]

/--
theorem `xor_iff_or_and_not_and` / 定理 `xor_iff_or_and_not_and`

English:
theorem xor_iff_or_and_not_and
  given: (a b : Prop)
  statement: Xor a b ↔ (a ∨ b) ∧ (¬(a ∧ b))
  proof: by
  rw [Xor]; rw [or_and_right]; rw [not_and_or]; rw [and_or_left]; rw [and_not_self_iff]; rw [false_or]; rw [and_or_left]; rw [and_not_self_iff]; rw [or_false]

中文:
定理 xor_iff_or_and_not_and
  条件: (a b : 命题)
  结论: Xor a b ↔ (a ∨ b) ∧ (¬(a ∧ b))
  证明: by
  rw [Xor]; rw [or_and_right]; rw [not_and_or]; rw [and_or_left]; rw [and_not_self_iff]; rw [false_or]; rw [and_or_left]; rw [and_not_self_iff]; rw [or_false]

Depends on / 依赖: and_not_self_iff, and_or_left, false_or, not_and_or, or_and_right, or_false
-/
theorem xor_iff_or_and_not_and (a b : Prop) : Xor a b ↔ (a ∨ b) ∧ (¬(a ∧ b)) := by
  rw [Xor]; rw [or_and_right]; rw [not_and_or]; rw [and_or_left]; rw [and_not_self_iff]; rw [false_or]; rw [and_or_left]; rw [and_not_self_iff]; rw [or_false]

end Propositional

/-! ### Declarations about equality -/

section Equality

-- todo: change name
/--
theorem `forall_cond_comm` / 定理 `forall_cond_comm`

English:
theorem forall_cond_comm
  given: {α} {s : α -> Prop} {p : α -> α -> Prop}
  proof: ⟨fun h a b ha hb => h a ha b hb, fun h a ha b hb => h a b ha hb⟩

中文:
定理 forall_cond_comm
  条件: {α} {s : α -> 命题} {p : α -> α -> 命题}
  证明: ⟨fun h a b ha hb => h a ha b hb, fun h a ha b hb => h a b ha hb⟩
-/
theorem forall_cond_comm {α} {s : α -> Prop} {p : α -> α -> Prop} :
    (forall a, s a -> forall b, s b -> p a b) ↔ forall a b, s a -> s b -> p a b :=
  ⟨fun h a b ha hb => h a ha b hb, fun h a ha b hb => h a b ha hb⟩

/--
theorem `forall_mem_comm` / 定理 `forall_mem_comm`

English:
theorem forall_mem_comm
  given: {α β} [Membership α β] {s : β} {p : α -> α -> Prop}
  proof: forall_cond_comm

中文:
定理 forall_mem_comm
  条件: {α β} [Membership α β] {s : β} {p : α -> α -> 命题}
  证明: forall_cond_comm

Depends on / 依赖: forall_cond_comm
-/
theorem forall_mem_comm {α β} [Membership α β] {s : β} {p : α -> α -> Prop} :
    (forall a (_ : a in s) b (_ : b in s), p a b) ↔ forall a b, a in s -> b in s -> p a b :=
  forall_cond_comm


/--
lemma `ne_of_eq_of_ne` / 引理 `ne_of_eq_of_ne`

English:
lemma ne_of_eq_of_ne
  given: {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ : b != c)
  statement: a != c
  proof: h₁.symm ▸ h₂

中文:
引理 ne_of_eq_of_ne
  条件: {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ : b != c)
  结论: a != c
  证明: h₁.symm ▸ h₂
-/
lemma ne_of_eq_of_ne {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ : b != c) : a != c := h₁.symm ▸ h₂
/--
lemma `ne_of_ne_of_eq` / 引理 `ne_of_ne_of_eq`

English:
lemma ne_of_ne_of_eq
  given: {α : Sort*} {a b c : α} (h₁ : a != b) (h₂ : b = c)
  statement: a != c
  proof: h₂ ▸ h₁

alias Eq.trans_ne := ne_of_eq_of_ne
alias Ne.trans_eq := ne_of_ne_of_eq

中文:
引理 ne_of_ne_of_eq
  条件: {α : Sort*} {a b c : α} (h₁ : a != b) (h₂ : b = c)
  结论: a != c
  证明: h₂ ▸ h₁

alias Eq.trans_ne := ne_of_eq_of_ne
alias Ne.trans_eq := ne_of_ne_of_eq
-/
lemma ne_of_ne_of_eq {α : Sort*} {a b c : α} (h₁ : a != b) (h₂ : b = c) : a != c := h₂ ▸ h₁

alias Eq.trans_ne := ne_of_eq_of_ne
alias Ne.trans_eq := ne_of_ne_of_eq

/--
theorem `eq_equivalence` / 定理 `eq_equivalence`

English:
theorem eq_equivalence
  given: {α : Sort*}
  statement: Equivalence (@Eq α)
  proof: ⟨Eq.refl, @Eq.symm _, @Eq.trans _⟩

中文:
定理 eq_equivalence
  条件: {α : Sort*}
  结论: Equivalence (@Eq α)
  证明: ⟨Eq.refl, @Eq.symm _, @Eq.trans _⟩

Depends on / 依赖: Eq.refl, Eq.symm, Eq.trans
-/
theorem eq_equivalence {α : Sort*} : Equivalence (@Eq α) :=
  ⟨Eq.refl, @Eq.symm _, @Eq.trans _⟩

-- @[simp] -- FIXME simp ignores proof rewrites
/--
theorem `congr_refl_left` / 定理 `congr_refl_left`

English:
theorem congr_refl_left
  given: {α β : Sort*} (f : α -> β) {a b : α} (h : a = b)
  proof: rfl

中文:
定理 congr_refl_left
  条件: {α β : Sort*} (f : α -> β) {a b : α} (h : a = b)
  证明: rfl
-/
theorem congr_refl_left {α β : Sort*} (f : α -> β) {a b : α} (h : a = b) :
    congr (Eq.refl f) h = congr_arg f h := rfl

-- @[simp] -- FIXME simp ignores proof rewrites
/--
theorem `congr_refl_right` / 定理 `congr_refl_right`

English:
theorem congr_refl_right
  given: {α β : Sort*} {f g : α -> β} (h : f = g) (a : α)
  proof: rfl

中文:
定理 congr_refl_right
  条件: {α β : Sort*} {f g : α -> β} (h : f = g) (a : α)
  证明: rfl
-/
theorem congr_refl_right {α β : Sort*} {f g : α -> β} (h : f = g) (a : α) :
    congr h (Eq.refl a) = congr_fun h a := rfl

-- @[simp] -- FIXME simp ignores proof rewrites
/--
theorem `congr_arg_refl` / 定理 `congr_arg_refl`

English:
theorem congr_arg_refl
  given: {α β : Sort*} (f : α -> β) (a : α)
  proof: rfl

中文:
定理 congr_arg_refl
  条件: {α β : Sort*} (f : α -> β) (a : α)
  证明: rfl
-/
theorem congr_arg_refl {α β : Sort*} (f : α -> β) (a : α) :
    congr_arg f (Eq.refl a) = Eq.refl (f a) :=
  rfl

-- @[simp] -- FIXME simp ignores proof rewrites
/--
theorem `congr_fun_rfl` / 定理 `congr_fun_rfl`

English:
theorem congr_fun_rfl
  given: {α β : Sort*} (f : α -> β) (a : α)
  statement: congr_fun (Eq.refl f) a = Eq.refl (f a)
  proof: rfl

中文:
定理 congr_fun_rfl
  条件: {α β : Sort*} (f : α -> β) (a : α)
  结论: congr_fun (Eq.refl f) a = Eq.refl (f a)
  证明: rfl
-/
theorem congr_fun_rfl {α β : Sort*} (f : α -> β) (a : α) : congr_fun (Eq.refl f) a = Eq.refl (f a) :=
  rfl

-- @[simp] -- FIXME simp ignores proof rewrites
/--
theorem `congr_fun_congr_arg` / 定理 `congr_fun_congr_arg`

English:
theorem congr_fun_congr_arg
  given: {α β γ : Sort*} (f : α -> β -> γ) {a a' : α} (p : a = a') (b : β)
  proof: rfl

中文:
定理 congr_fun_congr_arg
  条件: {α β γ : Sort*} (f : α -> β -> γ) {a a' : α} (p : a = a') (b : β)
  证明: rfl
-/
theorem congr_fun_congr_arg {α β γ : Sort*} (f : α -> β -> γ) {a a' : α} (p : a = a') (b : β) :
    congr_fun (congr_arg f p) b = congr_arg (fun a => f a b) p := rfl

/--
theorem `rec_heq_of_heq` / 定理 `rec_heq_of_heq`

English:
theorem rec_heq_of_heq
  statement: {α β : Sort _} {a b : α} {C : α -> Sort*} {x : C a} {y : β}
  proof: eqRec_heq_iff.mpr h

@[simp]

中文:
定理 rec_heq_of_heq
  结论: {α β : Sort _} {a b : α} {C : α -> Sort*} {x : C a} {y : β}
  证明: eqRec_heq_iff.mpr h

@[simp]

Depends on / 依赖: eqRec_heq_iff, eqRec_heq_iff.mpr
-/
theorem rec_heq_of_heq {α β : Sort _} {a b : α} {C : α -> Sort*} {x : C a} {y : β}
    (e : a = b) (h : x ≍ y) : e ▸ x ≍ y :=
  eqRec_heq_iff.mpr h

@[simp]
/--
theorem `cast_heq_iff_heq` / 定理 `cast_heq_iff_heq`

English:
theorem cast_heq_iff_heq
  given: {α β γ : Sort _} (e : α = β) (a : α) (c : γ)
  proof: by subst e; rfl

@[simp]

中文:
定理 cast_heq_iff_heq
  条件: {α β γ : Sort _} (e : α = β) (a : α) (c : γ)
  证明: by subst e; rfl

@[simp]
-/
theorem cast_heq_iff_heq {α β γ : Sort _} (e : α = β) (a : α) (c : γ) :
    cast e a ≍ c ↔ a ≍ c := by subst e; rfl

@[simp]
/--
theorem `heq_cast_iff_heq` / 定理 `heq_cast_iff_heq`

English:
theorem heq_cast_iff_heq
  given: {α β γ : Sort _} (e : β = γ) (a : α) (b : β)
  proof: by subst e; rfl

universe u

中文:
定理 heq_cast_iff_heq
  条件: {α β γ : Sort _} (e : β = γ) (a : α) (b : β)
  证明: by subst e; rfl

universe u
-/
theorem heq_cast_iff_heq {α β γ : Sort _} (e : β = γ) (a : α) (b : β) :
    a ≍ cast e b ↔ a ≍ b := by subst e; rfl

universe u
variable {α β : Sort u} {e : β = α} {a : α} {b : β}

/--
lemma `heq_of_eq_cast` / 引理 `heq_of_eq_cast`

English:
lemma heq_of_eq_cast
  given: (e : β = α)
  statement: a = cast e b -> a ≍ b
  proof: by rintro rfl; simp

中文:
引理 heq_of_eq_cast
  条件: (e : β = α)
  结论: a = cast e b -> a ≍ b
  证明: by rintro rfl; simp
-/
lemma heq_of_eq_cast (e : β = α) : a = cast e b -> a ≍ b := by rintro rfl; simp

/--
lemma `eq_cast_iff_heq` / 引理 `eq_cast_iff_heq`

English:
lemma eq_cast_iff_heq
  statement: a = cast e b ↔ a ≍ b
  proof: ⟨heq_of_eq_cast _, fun h => by cases h; rfl⟩

中文:
引理 eq_cast_iff_heq
  结论: a = cast e b ↔ a ≍ b
  证明: ⟨heq_of_eq_cast _, fun h => by cases h; rfl⟩

Depends on / 依赖: heq_of_eq_cast
-/
lemma eq_cast_iff_heq : a = cast e b ↔ a ≍ b := ⟨heq_of_eq_cast _, fun h => by cases h; rfl⟩

/--
lemma `heq_iff_exists_eq_cast` / 引理 `heq_iff_exists_eq_cast`

English:
lemma heq_iff_exists_eq_cast
  proof: ⟨fun h => ⟨type_eq_of_heq h.symm, eq_cast_iff_heq.mpr h⟩,
    by rintro ⟨rfl, h⟩; rw [h, cast_eq]⟩

中文:
引理 heq_iff_exists_eq_cast
  证明: ⟨fun h => ⟨type_eq_of_heq h.symm, eq_cast_iff_heq.mpr h⟩,
    by rintro ⟨rfl, h⟩; rw [h, cast_eq]⟩

Depends on / 依赖: cast_eq, eq_cast_iff_heq, eq_cast_iff_heq.mpr, h.symm, type_eq_of_heq
-/
lemma heq_iff_exists_eq_cast :
    a ≍ b ↔ exists (h : β = α), a = cast h b :=
  ⟨fun h => ⟨type_eq_of_heq h.symm, eq_cast_iff_heq.mpr h⟩,
    by rintro ⟨rfl, h⟩; rw [h, cast_eq]⟩

/--
lemma `heq_iff_exists_cast_eq` / 引理 `heq_iff_exists_cast_eq`

English:
lemma heq_iff_exists_cast_eq
  proof: by
  simp only [heq_comm (a := a), heq_iff_exists_eq_cast, eq_comm]

中文:
引理 heq_iff_exists_cast_eq
  证明: by
  simp only [heq_comm (a := a), heq_iff_exists_eq_cast, eq_comm]

Depends on / 依赖: eq_comm, heq_comm, heq_iff_exists_eq_cast
-/
lemma heq_iff_exists_cast_eq :
    a ≍ b ↔ exists (h : α = β), cast h a = b := by
  simp only [heq_comm (a := a), heq_iff_exists_eq_cast, eq_comm]

end Equality

/-! ### Declarations about quantifiers -/
section Quantifiers
section Dependent

variable {α : Sort*} {β : α -> Sort*} {γ : forall a, β a -> Sort*}

/--
theorem `forall₂_imp` / 定理 `forall₂_imp`

English:
theorem forall₂_imp
  given: {p q : forall a, β a -> Prop} (h : forall a b, p a b -> q a b)
  proof: forall_imp fun i => forall_imp h i

中文:
定理 forall₂_imp
  条件: {p q : 对任意 a, β a -> 命题} (h : 对任意 a b, p a b -> q a b)
  证明: forall_imp fun i => forall_imp h i

Depends on / 依赖: forall_imp
-/
theorem forall₂_imp {p q : forall a, β a -> Prop} (h : forall a b, p a b -> q a b) :
    (forall a b, p a b) -> forall a b, q a b :=
forall_imp fun i => forall_imp h i

/--
theorem `forall₃_imp` / 定理 `forall₃_imp`

English:
theorem forall₃_imp
  given: {p q : forall a b, γ a b -> Prop} (h : forall a b c, p a b c -> q a b c)
  proof: forall_imp fun a => forall₂_imp h a

中文:
定理 forall₃_imp
  条件: {p q : 对任意 a b, γ a b -> 命题} (h : 对任意 a b c, p a b c -> q a b c)
  证明: forall_imp fun a => forall₂_imp h a

Depends on / 依赖: forall_imp
-/
theorem forall₃_imp {p q : forall a b, γ a b -> Prop} (h : forall a b c, p a b c -> q a b c) :
    (forall a b c, p a b c) -> forall a b c, q a b c :=
forall_imp fun a => forall₂_imp h a

/--
theorem `Exists₂.imp` / 定理 `Exists₂.imp`

English:
theorem Exists₂.imp
  given: {p q : forall a, β a -> Prop} (h : forall a b, p a b -> q a b)
  proof: Exists.imp fun a => Exists.imp h a

中文:
定理 Exists₂.imp
  条件: {p q : 对任意 a, β a -> 命题} (h : 对任意 a b, p a b -> q a b)
  证明: Exists.imp fun a => Exists.imp h a

Depends on / 依赖: Exists, Exists.imp
-/
theorem Exists₂.imp {p q : forall a, β a -> Prop} (h : forall a b, p a b -> q a b) :
    (exists a b, p a b) -> exists a b, q a b :=
Exists.imp fun a => Exists.imp h a

/--
theorem `Exists₃.imp` / 定理 `Exists₃.imp`

English:
theorem Exists₃.imp
  given: {p q : forall a b, γ a b -> Prop} (h : forall a b c, p a b c -> q a b c)
  proof: Exists.imp fun a => Exists₂.imp h a

中文:
定理 Exists₃.imp
  条件: {p q : 对任意 a b, γ a b -> 命题} (h : 对任意 a b c, p a b c -> q a b c)
  证明: Exists.imp fun a => Exists₂.imp h a

Depends on / 依赖: Exists, Exists.imp
-/
theorem Exists₃.imp {p q : forall a b, γ a b -> Prop} (h : forall a b c, p a b c -> q a b c) :
    (exists a b c, p a b c) -> exists a b c, q a b c :=
Exists.imp fun a => Exists₂.imp h a

end Dependent

variable {α β : Sort*} {p : α -> Prop}

@[deprecated (since := "2026-03-25")] alias forall_swap := forall_comm

/--
theorem `forall₂_comm` / 定理 `forall₂_comm`

English:
theorem forall₂_comm
  proof: ⟨swap₂, swap₂⟩

@[deprecated (since := "2026-03-25")] alias forall₂_swap := forall₂_comm

中文:
定理 forall₂_comm
  证明: ⟨swap₂, swap₂⟩

@[deprecated (since := "2026-03-25")] alias forall₂_swap := forall₂_comm
-/
theorem forall₂_comm
    {ι₁ ι₂ : Sort*} {κ₁ : ι₁ -> Sort*} {κ₂ : ι₂ -> Sort*} {p : forall i₁, κ₁ i₁ -> forall i₂, κ₂ i₂ -> Prop} :
    (forall i₁ j₁ i₂ j₂, p i₁ j₁ i₂ j₂) ↔ forall i₂ j₂ i₁ j₁, p i₁ j₁ i₂ j₂ := ⟨swap₂, swap₂⟩

@[deprecated (since := "2026-03-25")] alias forall₂_swap := forall₂_comm

/--
theorem `imp_forall_iff` / 定理 `imp_forall_iff`

English:
theorem imp_forall_iff
  given: {α : Type*} {p : Prop} {q : α -> Prop}
  statement: (p -> forall x, q x) ↔ forall x, p -> q x
  proof: forall_comm

中文:
定理 imp_forall_iff
  条件: {α : 类型} {p : 命题} {q : α -> 命题}
  结论: (p -> 对任意 x, q x) ↔ 对任意 x, p -> q x
  证明: forall_comm

Depends on / 依赖: forall_comm
-/
theorem imp_forall_iff {α : Type*} {p : Prop} {q : α -> Prop} : (p -> forall x, q x) ↔ forall x, p -> q x :=
  forall_comm

/--
lemma `imp_forall_iff_forall` / 引理 `imp_forall_iff_forall`

English:
lemma imp_forall_iff_forall
  given: (A : Prop) (B : A -> Prop)
  statement: (A -> forall h : A, B h) ↔ forall h : A, B h
  proof: by
  by_cases h : A <;> simp [h]

@[deprecated (since := "2026-03-25")] alias exists_swap := exists_comm

中文:
引理 imp_forall_iff_forall
  条件: (A : 命题) (B : A -> 命题)
  结论: (A -> 对任意 h : A, B h) ↔ 对任意 h : A, B h
  证明: by
  by_cases h : A <;> simp [h]

@[deprecated (since := "2026-03-25")] alias exists_swap := exists_comm
-/
lemma imp_forall_iff_forall (A : Prop) (B : A -> Prop) : (A -> forall h : A, B h) ↔ forall h : A, B h := by
  by_cases h : A <;> simp [h]

@[deprecated (since := "2026-03-25")] alias exists_swap := exists_comm

/--
theorem `exists_and_exists_comm` / 定理 `exists_and_exists_comm`

English:
theorem exists_and_exists_comm
  given: {P : α -> Prop} {Q : β -> Prop}
  proof: ⟨fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ => ⟨a, b, ⟨ha, hb⟩⟩, fun ⟨a, b, ⟨ha, hb⟩⟩ => ⟨⟨a, ha⟩, ⟨b, hb⟩⟩⟩

中文:
定理 exists_and_exists_comm
  条件: {P : α -> 命题} {Q : β -> 命题}
  证明: ⟨fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ => ⟨a, b, ⟨ha, hb⟩⟩, fun ⟨a, b, ⟨ha, hb⟩⟩ => ⟨⟨a, ha⟩, ⟨b, hb⟩⟩⟩
-/
theorem exists_and_exists_comm {P : α -> Prop} {Q : β -> Prop} :
    (exists a, P a) ∧ (exists b, Q b) ↔ exists a b, P a ∧ Q b :=
  ⟨fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ => ⟨a, b, ⟨ha, hb⟩⟩, fun ⟨a, b, ⟨ha, hb⟩⟩ => ⟨⟨a, ha⟩, ⟨b, hb⟩⟩⟩

export Classical (not_forall)

/--
theorem `not_forall_not` / 定理 `not_forall_not`

English:
theorem not_forall_not
  statement: (¬forall x, ¬p x) ↔ exists x, p x
  proof: open scoped Classical in Decidable.not_forall_not

中文:
定理 not_forall_not
  结论: (¬对任意 x, ¬p x) ↔ 存在 x, p x
  证明: open scoped Classical in Decidable.not_forall_not

Depends on / 依赖: Classical, Decidable, Decidable.not_forall_not, not_forall_not, scoped
-/
theorem not_forall_not : (¬forall x, ¬p x) ↔ exists x, p x :=
  open scoped Classical in Decidable.not_forall_not

export Classical (not_exists_not)

/--
lemma `forall_or_exists_not` / 引理 `forall_or_exists_not`

English:
lemma forall_or_exists_not
  given: (P : α -> Prop)
  statement: (forall a, P a) ∨ exists a, ¬P a
  proof: by
  rw [← not_forall]; exact em _

中文:
引理 forall_or_exists_not
  条件: (P : α -> 命题)
  结论: (对任意 a, P a) ∨ 存在 a, ¬P a
  证明: by
  rw [← not_forall]; exact em _

Depends on / 依赖: not_forall
-/
lemma forall_or_exists_not (P : α -> Prop) : (forall a, P a) ∨ exists a, ¬P a := by
  rw [← not_forall]; exact em _

/--
lemma `exists_or_forall_not` / 引理 `exists_or_forall_not`

English:
lemma exists_or_forall_not
  given: (P : α -> Prop)
  statement: (exists a, P a) ∨ forall a, ¬P a
  proof: by
  rw [← not_exists]; exact em _

中文:
引理 exists_or_forall_not
  条件: (P : α -> 命题)
  结论: (存在 a, P a) ∨ 对任意 a, ¬P a
  证明: by
  rw [← not_exists]; exact em _

Depends on / 依赖: not_exists
-/
lemma exists_or_forall_not (P : α -> Prop) : (exists a, P a) ∨ forall a, ¬P a := by
  rw [← not_exists]; exact em _

/--
theorem `forall_imp_iff_exists_imp` / 定理 `forall_imp_iff_exists_imp`

English:
theorem forall_imp_iff_exists_imp
  given: {α : Sort*} {p : α -> Prop} {b : Prop} [ha : Nonempty α]
  proof: by
  classical
  let ⟨a⟩ := ha
  refine ⟨fun h => not_forall_not.1 fun h' => ?_, fun ⟨x, hx⟩ h => hx (h x)⟩
exact if hb : b then h' a fun _ => hb else hb h fun x => (Classical.not_imp.1 (h' x)).1

@[mfld_simps]

中文:
定理 forall_imp_iff_exists_imp
  条件: {α : Sort*} {p : α -> 命题} {b : 命题} [ha : Nonempty α]
  证明: by
  classical
  let ⟨a⟩ := ha
  refine ⟨fun h => not_forall_not.1 fun h' => ?_, fun ⟨x, hx⟩ h => hx (h x)⟩
exact if hb : b then h' a fun _ => hb else hb h fun x => (Classical.not_imp.1 (h' x)).1

@[mfld_simps]

Depends on / 依赖: Classical, Classical.not_imp, classical, not_forall_not, not_imp
-/
theorem forall_imp_iff_exists_imp {α : Sort*} {p : α -> Prop} {b : Prop} [ha : Nonempty α] :
    (forall x, p x) -> b ↔ exists x, p x -> b := by
  classical
  let ⟨a⟩ := ha
  refine ⟨fun h => not_forall_not.1 fun h' => ?_, fun ⟨x, hx⟩ h => hx (h x)⟩
exact if hb : b then h' a fun _ => hb else hb h fun x => (Classical.not_imp.1 (h' x)).1

@[mfld_simps]
/--
theorem `forall_true_iff` / 定理 `forall_true_iff`

English:
theorem forall_true_iff
  statement: (α -> True) ↔ True
  proof: imp_true_iff _

中文:
定理 forall_true_iff
  结论: (α -> True) ↔ True
  证明: imp_true_iff _

Depends on / 依赖: imp_true_iff
-/
theorem forall_true_iff : (α -> True) ↔ True := imp_true_iff _

-- Unfortunately this causes simp to loop sometimes, so we
-- add the 2 and 3 cases as simp lemmas instead
/--
theorem `forall_true_iff'` / 定理 `forall_true_iff'`

English:
theorem forall_true_iff'
  given: (h : forall a, p a ↔ True)
  statement: (forall a, p a) ↔ True
  proof: iff_true_intro fun _ => of_iff_true (h _)

中文:
定理 forall_true_iff'
  条件: (h : 对任意 a, p a ↔ True)
  结论: (对任意 a, p a) ↔ True
  证明: iff_true_intro fun _ => of_iff_true (h _)

Depends on / 依赖: iff_true_intro, of_iff_true
-/
theorem forall_true_iff' (h : forall a, p a ↔ True) : (forall a, p a) ↔ True :=
  iff_true_intro fun _ => of_iff_true (h _)

-- This is not marked `@[simp]` because `implies_true : (α → True) = True` works
/--
theorem `forall₂_true_iff` / 定理 `forall₂_true_iff`

English:
theorem forall₂_true_iff
  given: {β : α -> Sort*}
  statement: (forall a, β a -> True) ↔ True
  proof: by simp

中文:
定理 forall₂_true_iff
  条件: {β : α -> Sort*}
  结论: (对任意 a, β a -> True) ↔ True
  证明: by simp
-/
theorem forall₂_true_iff {β : α -> Sort*} : (forall a, β a -> True) ↔ True := by simp

-- This is not marked `@[simp]` because `implies_true : (α → True) = True` works
/--
theorem `forall₃_true_iff` / 定理 `forall₃_true_iff`

English:
theorem forall₃_true_iff
  given: {β : α -> Sort*} {γ : forall a, β a -> Sort*}
  proof: by simp

中文:
定理 forall₃_true_iff
  条件: {β : α -> Sort*} {γ : 对任意 a, β a -> Sort*}
  证明: by simp
-/
theorem forall₃_true_iff {β : α -> Sort*} {γ : forall a, β a -> Sort*} :
    (forall (a) (b : β a), γ a b -> True) ↔ True := by simp

/--
theorem `Decidable.and_forall_ne` / 定理 `Decidable.and_forall_ne`

English:
theorem Decidable.and_forall_ne
  given: [DecidableEq α] (a : α) {p : α -> Prop}
  proof: by
  simp only [← @forall_eq _ p a, ← forall_and, ← or_imp, Decidable.em, forall_const]

中文:
定理 Decidable.and_forall_ne
  条件: [DecidableEq α] (a : α) {p : α -> 命题}
  证明: by
  simp only [← @forall_eq _ p a, ← forall_and, ← or_imp, Decidable.em, forall_const]

Depends on / 依赖: Decidable, Decidable.em, forall_and, forall_const, forall_eq, or_imp
-/
theorem Decidable.and_forall_ne [DecidableEq α] (a : α) {p : α -> Prop} :
    (p a ∧ forall b, b != a -> p b) ↔ forall b, p b := by
  simp only [← @forall_eq _ p a, ← forall_and, ← or_imp, Decidable.em, forall_const]

/--
theorem `and_forall_ne` / 定理 `and_forall_ne`

English:
theorem and_forall_ne
  given: (a : α)
  statement: (p a ∧ forall b, b != a -> p b) ↔ forall b, p b
  proof: open scoped Classical in Decidable.and_forall_ne a

中文:
定理 and_forall_ne
  条件: (a : α)
  结论: (p a ∧ 对任意 b, b != a -> p b) ↔ 对任意 b, p b
  证明: open scoped Classical in Decidable.and_forall_ne a

Depends on / 依赖: Classical, Decidable, Decidable.and_forall_ne, and_forall_ne, scoped
-/
theorem and_forall_ne (a : α) : (p a ∧ forall b, b != a -> p b) ↔ forall b, p b :=
  open scoped Classical in Decidable.and_forall_ne a

/--
theorem `Ne.ne_or_ne` / 定理 `Ne.ne_or_ne`

English:
theorem Ne.ne_or_ne
  given: {x y : α} (z : α) (h : x != y)
  statement: x != z ∨ y != z
  proof: not_and_or.1 mt (and_imp.2 (· ▸ ·)) h.symm

@[simp]

中文:
定理 Ne.ne_or_ne
  条件: {x y : α} (z : α) (h : x != y)
  结论: x != z ∨ y != z
  证明: not_and_or.1 mt (and_imp.2 (· ▸ ·)) h.symm

@[simp]

Depends on / 依赖: and_imp, h.symm, not_and_or
-/
theorem Ne.ne_or_ne {x y : α} (z : α) (h : x != y) : x != z ∨ y != z :=
not_and_or.1 mt (and_imp.2 (· ▸ ·)) h.symm

@[simp]
/--
theorem `exists_apply_eq_apply'` / 定理 `exists_apply_eq_apply'`

English:
theorem exists_apply_eq_apply'
  given: (f : α -> β) (a' : α)
  statement: exists a, f a' = f a
  proof: ⟨a', rfl⟩

@[simp]

中文:
定理 exists_apply_eq_apply'
  条件: (f : α -> β) (a' : α)
  结论: 存在 a, f a' = f a
  证明: ⟨a', rfl⟩

@[simp]
-/
theorem exists_apply_eq_apply' (f : α -> β) (a' : α) : exists a, f a' = f a := ⟨a', rfl⟩

@[simp]
/--
lemma `exists_apply_eq_apply2` / 引理 `exists_apply_eq_apply2`

English:
lemma exists_apply_eq_apply2
  given: {α β γ} {f : α -> β -> γ} {a : α} {b : β}
  statement: exists x y, f x y = f a b
  proof: ⟨a, b, rfl⟩

@[simp]

中文:
引理 exists_apply_eq_apply2
  条件: {α β γ} {f : α -> β -> γ} {a : α} {b : β}
  结论: 存在 x y, f x y = f a b
  证明: ⟨a, b, rfl⟩

@[simp]
-/
lemma exists_apply_eq_apply2 {α β γ} {f : α -> β -> γ} {a : α} {b : β} : exists x y, f x y = f a b :=
  ⟨a, b, rfl⟩

@[simp]
/--
lemma `exists_apply_eq_apply2'` / 引理 `exists_apply_eq_apply2'`

English:
lemma exists_apply_eq_apply2'
  given: {α β γ} {f : α -> β -> γ} {a : α} {b : β}
  statement: exists x y, f a b = f x y
  proof: ⟨a, b, rfl⟩

@[simp]

中文:
引理 exists_apply_eq_apply2'
  条件: {α β γ} {f : α -> β -> γ} {a : α} {b : β}
  结论: 存在 x y, f a b = f x y
  证明: ⟨a, b, rfl⟩

@[simp]
-/
lemma exists_apply_eq_apply2' {α β γ} {f : α -> β -> γ} {a : α} {b : β} : exists x y, f a b = f x y :=
  ⟨a, b, rfl⟩

@[simp]
/--
lemma `exists_apply_eq_apply3` / 引理 `exists_apply_eq_apply3`

English:
lemma exists_apply_eq_apply3
  given: {α β γ δ} {f : α -> β -> γ -> δ} {a : α} {b : β} {c : γ}
  proof: ⟨a, b, c, rfl⟩

@[simp]

中文:
引理 exists_apply_eq_apply3
  条件: {α β γ δ} {f : α -> β -> γ -> δ} {a : α} {b : β} {c : γ}
  证明: ⟨a, b, c, rfl⟩

@[simp]
-/
lemma exists_apply_eq_apply3 {α β γ δ} {f : α -> β -> γ -> δ} {a : α} {b : β} {c : γ} :
    exists x y z, f x y z = f a b c :=
  ⟨a, b, c, rfl⟩

@[simp]
/--
lemma `exists_apply_eq_apply3'` / 引理 `exists_apply_eq_apply3'`

English:
lemma exists_apply_eq_apply3'
  given: {α β γ δ} {f : α -> β -> γ -> δ} {a : α} {b : β} {c : γ}
  proof: ⟨a, b, c, rfl⟩

中文:
引理 exists_apply_eq_apply3'
  条件: {α β γ δ} {f : α -> β -> γ -> δ} {a : α} {b : β} {c : γ}
  证明: ⟨a, b, c, rfl⟩
-/
lemma exists_apply_eq_apply3' {α β γ δ} {f : α -> β -> γ -> δ} {a : α} {b : β} {c : γ} :
    exists x y z, f a b c = f x y z :=
  ⟨a, b, c, rfl⟩

/--
theorem `exists_apply_eq` / 定理 `exists_apply_eq`

English:
theorem exists_apply_eq
  given: (a : α) (b : β)
  statement: exists f : α -> β, f a = b
  proof: ⟨fun _ => b, rfl⟩

中文:
定理 exists_apply_eq
  条件: (a : α) (b : β)
  结论: 存在 f : α -> β, f a = b
  证明: ⟨fun _ => b, rfl⟩
-/
theorem exists_apply_eq (a : α) (b : β) : exists f : α -> β, f a = b := ⟨fun _ => b, rfl⟩

/--
theorem `exists_exists_and_eq_and` / 定理 `exists_exists_and_eq_and`

English:
theorem exists_exists_and_eq_and
  given: {f : α -> β} {p : α -> Prop} {q : β -> Prop}
  proof: ⟨fun ⟨_, ⟨a, ha, hab⟩, hb⟩ => ⟨a, ha, hab.symm ▸ hb⟩, fun ⟨a, hp, hq⟩ => ⟨f a, ⟨a, hp, rfl⟩, hq⟩⟩

中文:
定理 exists_exists_and_eq_and
  条件: {f : α -> β} {p : α -> 命题} {q : β -> 命题}
  证明: ⟨fun ⟨_, ⟨a, ha, hab⟩, hb⟩ => ⟨a, ha, hab.symm ▸ hb⟩, fun ⟨a, hp, hq⟩ => ⟨f a, ⟨a, hp, rfl⟩, hq⟩⟩
-/
@[simp] theorem exists_exists_and_eq_and {f : α -> β} {p : α -> Prop} {q : β -> Prop} :
    (exists b, (exists a, p a ∧ f a = b) ∧ q b) ↔ exists a, p a ∧ q (f a) :=
  ⟨fun ⟨_, ⟨a, ha, hab⟩, hb⟩ => ⟨a, ha, hab.symm ▸ hb⟩, fun ⟨a, hp, hq⟩ => ⟨f a, ⟨a, hp, rfl⟩, hq⟩⟩

/--
theorem `exists_exists_eq_and` / 定理 `exists_exists_eq_and`

English:
theorem exists_exists_eq_and
  given: {f : α -> β} {p : β -> Prop}
  proof: ⟨fun ⟨_, ⟨a, ha⟩, hb⟩ => ⟨a, ha.symm ▸ hb⟩, fun ⟨a, ha⟩ => ⟨f a, ⟨a, rfl⟩, ha⟩⟩

中文:
定理 exists_exists_eq_and
  条件: {f : α -> β} {p : β -> 命题}
  证明: ⟨fun ⟨_, ⟨a, ha⟩, hb⟩ => ⟨a, ha.symm ▸ hb⟩, fun ⟨a, ha⟩ => ⟨f a, ⟨a, rfl⟩, ha⟩⟩
-/
@[simp] theorem exists_exists_eq_and {f : α -> β} {p : β -> Prop} :
    (exists b, (exists a, f a = b) ∧ p b) ↔ exists a, p (f a) :=
  ⟨fun ⟨_, ⟨a, ha⟩, hb⟩ => ⟨a, ha.symm ▸ hb⟩, fun ⟨a, ha⟩ => ⟨f a, ⟨a, rfl⟩, ha⟩⟩

/--
theorem `exists_exists_and_exists_and_eq_and` / 定理 `exists_exists_and_exists_and_eq_and`

English:
theorem exists_exists_and_exists_and_eq_and
  statement: {α β γ : Type*}
  proof: ⟨fun ⟨_, ⟨a, ha, b, hb, hab⟩, hc⟩ => ⟨a, ha, b, hb, hab.symm ▸ hc⟩,
    fun ⟨a, ha, b, hb, hab⟩ => ⟨f a b, ⟨a, ha, b, hb, rfl⟩, hab⟩⟩

中文:
定理 exists_exists_and_exists_and_eq_and
  结论: {α β γ : 类型}
  证明: ⟨fun ⟨_, ⟨a, ha, b, hb, hab⟩, hc⟩ => ⟨a, ha, b, hb, hab.symm ▸ hc⟩,
    fun ⟨a, ha, b, hb, hab⟩ => ⟨f a b, ⟨a, ha, b, hb, rfl⟩, hab⟩⟩
-/
@[simp] theorem exists_exists_and_exists_and_eq_and {α β γ : Type*}
    {f : α -> β -> γ} {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop} :
    (exists c, (exists a, p a ∧ exists b, q b ∧ f a b = c) ∧ r c) ↔ exists a, p a ∧ exists b, q b ∧ r (f a b) :=
  ⟨fun ⟨_, ⟨a, ha, b, hb, hab⟩, hc⟩ => ⟨a, ha, b, hb, hab.symm ▸ hc⟩,
    fun ⟨a, ha, b, hb, hab⟩ => ⟨f a b, ⟨a, ha, b, hb, rfl⟩, hab⟩⟩

/--
theorem `exists_exists_exists_and_eq` / 定理 `exists_exists_exists_and_eq`

English:
theorem exists_exists_exists_and_eq
  statement: {α β γ : Type*}
  proof: ⟨fun ⟨_, ⟨a, b, hab⟩, hc⟩ => ⟨a, b, hab.symm ▸ hc⟩,
    fun ⟨a, b, hab⟩ => ⟨f a b, ⟨a, b, rfl⟩, hab⟩⟩

中文:
定理 exists_exists_exists_and_eq
  结论: {α β γ : 类型}
  证明: ⟨fun ⟨_, ⟨a, b, hab⟩, hc⟩ => ⟨a, b, hab.symm ▸ hc⟩,
    fun ⟨a, b, hab⟩ => ⟨f a b, ⟨a, b, rfl⟩, hab⟩⟩
-/
@[simp] theorem exists_exists_exists_and_eq {α β γ : Type*}
    {f : α -> β -> γ} {p : γ -> Prop} :
    (exists c, (exists a, exists b, f a b = c) ∧ p c) ↔ exists a, exists b, p (f a b) :=
  ⟨fun ⟨_, ⟨a, b, hab⟩, hc⟩ => ⟨a, b, hab.symm ▸ hc⟩,
    fun ⟨a, b, hab⟩ => ⟨f a b, ⟨a, b, rfl⟩, hab⟩⟩

/--
theorem `forall_apply_eq_imp_iff'` / 定理 `forall_apply_eq_imp_iff'`

English:
theorem forall_apply_eq_imp_iff'
  given: {f : α -> β} {p : β -> Prop}
  proof: by simp

中文:
定理 forall_apply_eq_imp_iff'
  条件: {f : α -> β} {p : β -> 命题}
  证明: by simp
-/
theorem forall_apply_eq_imp_iff' {f : α -> β} {p : β -> Prop} :
    (forall a b, f a = b -> p b) ↔ forall a, p (f a) := by simp

/--
theorem `forall_eq_apply_imp_iff'` / 定理 `forall_eq_apply_imp_iff'`

English:
theorem forall_eq_apply_imp_iff'
  given: {f : α -> β} {p : β -> Prop}
  proof: by simp

中文:
定理 forall_eq_apply_imp_iff'
  条件: {f : α -> β} {p : β -> 命题}
  证明: by simp
-/
theorem forall_eq_apply_imp_iff' {f : α -> β} {p : β -> Prop} :
    (forall a b, b = f a -> p b) ↔ forall a, p (f a) := by simp

/--
theorem `exists₂_comm` / 定理 `exists₂_comm`

English:
theorem exists₂_comm
  proof: by
  simp only [@exists_comm (κ₁ _), @exists_comm ι₁]

中文:
定理 exists₂_comm
  证明: by
  simp only [@exists_comm (κ₁ _), @exists_comm ι₁]

Depends on / 依赖: exists_comm
-/
theorem exists₂_comm
    {ι₁ ι₂ : Sort*} {κ₁ : ι₁ -> Sort*} {κ₂ : ι₂ -> Sort*} {p : forall i₁, κ₁ i₁ -> forall i₂, κ₂ i₂ -> Prop} :
    (exists i₁ j₁ i₂ j₂, p i₁ j₁ i₂ j₂) ↔ exists i₂ j₂ i₁ j₁, p i₁ j₁ i₂ j₂ := by
  simp only [@exists_comm (κ₁ _), @exists_comm ι₁]

/--
theorem `And.exists` / 定理 `And.exists`

English:
theorem And.exists
  given: {p q : Prop} {f : p ∧ q -> Prop}
  statement: (exists h, f h) ↔ exists hp hq, f ⟨hp, hq⟩
  proof: ⟨fun ⟨h, H⟩ => ⟨h.1, h.2, H⟩, fun ⟨hp, hq, H⟩ => ⟨⟨hp, hq⟩, H⟩⟩

中文:
定理 And.exists
  条件: {p q : 命题} {f : p ∧ q -> 命题}
  结论: (存在 h, f h) ↔ 存在 hp hq, f ⟨hp, hq⟩
  证明: ⟨fun ⟨h, H⟩ => ⟨h.1, h.2, H⟩, fun ⟨hp, hq, H⟩ => ⟨⟨hp, hq⟩, H⟩⟩
-/
theorem And.exists {p q : Prop} {f : p ∧ q -> Prop} : (exists h, f h) ↔ exists hp hq, f ⟨hp, hq⟩ :=
  ⟨fun ⟨h, H⟩ => ⟨h.1, h.2, H⟩, fun ⟨hp, hq, H⟩ => ⟨⟨hp, hq⟩, H⟩⟩

/--
theorem `forall_or_of_or_forall` / 定理 `forall_or_of_or_forall`

English:
theorem forall_or_of_or_forall
  given: {α : Sort*} {p : α -> Prop} {b : Prop} (h : b ∨ forall x, p x) (x : α)
  proof: h.imp_right fun h₂ => h₂ x

中文:
定理 forall_or_of_or_forall
  条件: {α : Sort*} {p : α -> 命题} {b : 命题} (h : b ∨ 对任意 x, p x) (x : α)
  证明: h.imp_right fun h₂ => h₂ x

Depends on / 依赖: h.imp_right, imp_right
-/
theorem forall_or_of_or_forall {α : Sort*} {p : α -> Prop} {b : Prop} (h : b ∨ forall x, p x) (x : α) :
    b ∨ p x :=
  h.imp_right fun h₂ => h₂ x

-- See Note [decidable namespace]
/--
theorem `Decidable.forall_or_left` / 定理 `Decidable.forall_or_left`

English:
theorem Decidable.forall_or_left
  given: {q : Prop} {p : α -> Prop} [Decidable q]
  proof: ⟨fun h => if hq : q then Or.inl hq else
    Or.inr fun x => (h x).resolve_left hq, forall_or_of_or_forall⟩

中文:
定理 Decidable.forall_or_left
  条件: {q : 命题} {p : α -> 命题} [Decidable q]
  证明: ⟨fun h => if hq : q then Or.inl hq else
    Or.inr fun x => (h x).resolve_left hq, forall_or_of_or_forall⟩
-/
protected theorem Decidable.forall_or_left {q : Prop} {p : α -> Prop} [Decidable q] :
    (forall x, q ∨ p x) ↔ q ∨ forall x, p x :=
  ⟨fun h => if hq : q then Or.inl hq else
    Or.inr fun x => (h x).resolve_left hq, forall_or_of_or_forall⟩

/--
theorem `forall_or_left` / 定理 `forall_or_left`

English:
theorem forall_or_left
  given: {q} {p : α -> Prop}
  statement: (forall x, q ∨ p x) ↔ q ∨ forall x, p x
  proof: open scoped Classical in Decidable.forall_or_left

中文:
定理 forall_or_left
  条件: {q} {p : α -> 命题}
  结论: (对任意 x, q ∨ p x) ↔ q ∨ 对任意 x, p x
  证明: open scoped Classical in Decidable.forall_or_left

Depends on / 依赖: Classical, Decidable, Decidable.forall_or_left, forall_or_left, scoped
-/
theorem forall_or_left {q} {p : α -> Prop} : (forall x, q ∨ p x) ↔ q ∨ forall x, p x :=
  open scoped Classical in Decidable.forall_or_left

-- See Note [decidable namespace]
/--
theorem `Decidable.forall_or_right` / 定理 `Decidable.forall_or_right`

English:
theorem Decidable.forall_or_right
  given: {q} {p : α -> Prop} [Decidable q]
  proof: by simp [or_comm, Decidable.forall_or_left]

中文:
定理 Decidable.forall_or_right
  条件: {q} {p : α -> 命题} [Decidable q]
  证明: by simp [or_comm, Decidable.forall_or_left]
-/
protected theorem Decidable.forall_or_right {q} {p : α -> Prop} [Decidable q] :
    (forall x, p x ∨ q) ↔ (forall x, p x) ∨ q := by simp [or_comm, Decidable.forall_or_left]

/--
theorem `forall_or_right` / 定理 `forall_or_right`

English:
theorem forall_or_right
  given: {q} {p : α -> Prop}
  statement: (forall x, p x ∨ q) ↔ (forall x, p x) ∨ q
  proof: open scoped Classical in Decidable.forall_or_right

@[simp]

中文:
定理 forall_or_right
  条件: {q} {p : α -> 命题}
  结论: (对任意 x, p x ∨ q) ↔ (对任意 x, p x) ∨ q
  证明: open scoped Classical in Decidable.forall_or_right

@[simp]

Depends on / 依赖: Classical, Decidable, Decidable.forall_or_right, forall_or_right, scoped
-/
theorem forall_or_right {q} {p : α -> Prop} : (forall x, p x ∨ q) ↔ (forall x, p x) ∨ q :=
  open scoped Classical in Decidable.forall_or_right

@[simp]
/--
theorem `forall_and_index` / 定理 `forall_and_index`

English:
theorem forall_and_index
  given: {p q : Prop} {r : p ∧ q -> Prop}
  proof: ⟨fun h hp hq => h ⟨hp, hq⟩, fun h h1 => h h1.1 h1.2⟩

中文:
定理 forall_and_index
  条件: {p q : 命题} {r : p ∧ q -> 命题}
  证明: ⟨fun h hp hq => h ⟨hp, hq⟩, fun h h1 => h h1.1 h1.2⟩
-/
theorem forall_and_index {p q : Prop} {r : p ∧ q -> Prop} :
    (forall h : p ∧ q, r h) ↔ forall (hp : p) (hq : q), r ⟨hp, hq⟩ :=
  ⟨fun h hp hq => h ⟨hp, hq⟩, fun h h1 => h h1.1 h1.2⟩

/--
theorem `forall_and_index'` / 定理 `forall_and_index'`

English:
theorem forall_and_index'
  given: {p q : Prop} {r : p -> q -> Prop}
  proof: (forall_and_index (r := fun h => r h.1 h.2)).symm

中文:
定理 forall_and_index'
  条件: {p q : 命题} {r : p -> q -> 命题}
  证明: (forall_and_index (r := fun h => r h.1 h.2)).symm

Depends on / 依赖: forall_and_index
-/
theorem forall_and_index' {p q : Prop} {r : p -> q -> Prop} :
    (forall (hp : p) (hq : q), r hp hq) ↔ forall h : p ∧ q, r h.1 h.2 :=
  (forall_and_index (r := fun h => r h.1 h.2)).symm

/--
theorem `Exists.fst` / 定理 `Exists.fst`

English:
theorem Exists.fst
  given: {b : Prop} {p : b -> Prop}
  statement: Exists p -> b

中文:
定理 Exists.fst
  条件: {b : 命题} {p : b -> 命题}
  结论: Exists p -> b
-/
theorem Exists.fst {b : Prop} {p : b -> Prop} : Exists p -> b
  | ⟨h, _⟩ => h

/--
theorem `Exists.snd` / 定理 `Exists.snd`

English:
theorem Exists.snd
  given: {b : Prop} {p : b -> Prop}
  statement: forall h : Exists p, p h.fst

中文:
定理 Exists.snd
  条件: {b : 命题} {p : b -> 命题}
  结论: 对任意 h : Exists p, p h.fst
-/
theorem Exists.snd {b : Prop} {p : b -> Prop} : forall h : Exists p, p h.fst
  | ⟨_, h⟩ => h

/--
theorem `Prop.exists_iff` / 定理 `Prop.exists_iff`

English:
theorem Prop.exists_iff
  given: {p : Prop -> Prop}
  statement: (exists h, p h) ↔ p False ∨ p True
  proof: ⟨fun ⟨h₁, h₂⟩ => by_cases (fun H : h₁ => .inr <| by simpa only [H] using h₂)
    (fun H => .inl <| by simpa only [H] using h₂), fun h => h.elim (.intro _) (.intro _)⟩

中文:
定理 Prop.exists_iff
  条件: {p : 命题 -> 命题}
  结论: (存在 h, p h) ↔ p False ∨ p True
  证明: ⟨fun ⟨h₁, h₂⟩ => by_cases (fun H : h₁ => .inr <| by simpa only [H] using h₂)
    (fun H => .inl <| by simpa only [H] using h₂), fun h => h.elim (.intro _) (.intro _)⟩

Depends on / 依赖: h.elim
-/
theorem Prop.exists_iff {p : Prop -> Prop} : (exists h, p h) ↔ p False ∨ p True :=
  ⟨fun ⟨h₁, h₂⟩ => by_cases (fun H : h₁ => .inr <| by simpa only [H] using h₂)
    (fun H => .inl <| by simpa only [H] using h₂), fun h => h.elim (.intro _) (.intro _)⟩

/--
theorem `Prop.forall_iff` / 定理 `Prop.forall_iff`

English:
theorem Prop.forall_iff
  given: {p : Prop -> Prop}
  statement: (forall h, p h) ↔ p False ∧ p True
  proof: ⟨fun H => ⟨H _, H _⟩, fun ⟨h₁, h₂⟩ h => by by_cases H : h <;> simpa only [H]⟩

中文:
定理 Prop.forall_iff
  条件: {p : 命题 -> 命题}
  结论: (对任意 h, p h) ↔ p False ∧ p True
  证明: ⟨fun H => ⟨H _, H _⟩, fun ⟨h₁, h₂⟩ h => by by_cases H : h <;> simpa only [H]⟩
-/
theorem Prop.forall_iff {p : Prop -> Prop} : (forall h, p h) ↔ p False ∧ p True :=
  ⟨fun H => ⟨H _, H _⟩, fun ⟨h₁, h₂⟩ h => by by_cases H : h <;> simpa only [H]⟩

/--
theorem `exists_iff_of_forall` / 定理 `exists_iff_of_forall`

English:
theorem exists_iff_of_forall
  given: {p : Prop} {q : p -> Prop} (h : forall h, q h)
  statement: (exists h, q h) ↔ p
  proof: ⟨Exists.fst, fun H => ⟨H, h H⟩⟩

中文:
定理 exists_iff_of_forall
  条件: {p : 命题} {q : p -> 命题} (h : 对任意 h, q h)
  结论: (存在 h, q h) ↔ p
  证明: ⟨Exists.fst, fun H => ⟨H, h H⟩⟩

Depends on / 依赖: Exists, Exists.fst
-/
theorem exists_iff_of_forall {p : Prop} {q : p -> Prop} (h : forall h, q h) : (exists h, q h) ↔ p :=
  ⟨Exists.fst, fun H => ⟨H, h H⟩⟩

/--
theorem `exists_prop_of_false` / 定理 `exists_prop_of_false`

English:
theorem exists_prop_of_false
  given: {p : Prop} {q : p -> Prop}
  statement: ¬p -> ¬exists h' : p, q h'
  proof: mt Exists.fst

中文:
定理 exists_prop_of_false
  条件: {p : 命题} {q : p -> 命题}
  结论: ¬p -> ¬存在 h' : p, q h'
  证明: mt Exists.fst

Depends on / 依赖: Exists, Exists.fst
-/
theorem exists_prop_of_false {p : Prop} {q : p -> Prop} : ¬p -> ¬exists h' : p, q h' :=
  mt Exists.fst


/--
theorem `forall_prop_congr` / 定理 `forall_prop_congr`

English:
theorem forall_prop_congr
  given: {p p' : Prop} {q q' : p -> Prop} (hq : forall h, q h ↔ q' h) (hp : p ↔ p')
  proof: ⟨fun h1 h2 => (hq _).1 (h1 (hp.2 h2)), fun h1 h2 => (hq _).2 (h1 (hp.1 h2))⟩

中文:
定理 forall_prop_congr
  条件: {p p' : 命题} {q q' : p -> 命题} (hq : 对任意 h, q h ↔ q' h) (hp : p ↔ p')
  证明: ⟨fun h1 h2 => (hq _).1 (h1 (hp.2 h2)), fun h1 h2 => (hq _).2 (h1 (hp.1 h2))⟩
-/
theorem forall_prop_congr {p p' : Prop} {q q' : p -> Prop} (hq : forall h, q h ↔ q' h) (hp : p ↔ p') :
    (forall h, q h) ↔ forall h : p', q' (hp.2 h) :=
  ⟨fun h1 h2 => (hq _).1 (h1 (hp.2 h2)), fun h1 h2 => (hq _).2 (h1 (hp.1 h2))⟩

/--
theorem `forall_prop_congr'` / 定理 `forall_prop_congr'`

English:
theorem forall_prop_congr'
  given: {p p' : Prop} {q q' : p -> Prop} (hq : forall h, q h ↔ q' h) (hp : p ↔ p')
  proof: propext (forall_prop_congr hq hp)

中文:
定理 forall_prop_congr'
  条件: {p p' : 命题} {q q' : p -> 命题} (hq : 对任意 h, q h ↔ q' h) (hp : p ↔ p')
  证明: propext (forall_prop_congr hq hp)

Depends on / 依赖: forall_prop_congr, propext
-/
theorem forall_prop_congr' {p p' : Prop} {q q' : p -> Prop} (hq : forall h, q h ↔ q' h) (hp : p ↔ p') :
    (forall h, q h) = forall h : p', q' (hp.2 h) :=
  propext (forall_prop_congr hq hp)

/--
lemma `imp_congr_eq` / 引理 `imp_congr_eq`

English:
lemma imp_congr_eq
  given: {a b c d : Prop} (h₁ : a = c) (h₂ : b = d)
  statement: (a -> b) = (c -> d)
  proof: propext (imp_congr h₁.to_iff h₂.to_iff)

中文:
引理 imp_congr_eq
  条件: {a b c d : 命题} (h₁ : a = c) (h₂ : b = d)
  结论: (a -> b) = (c -> d)
  证明: propext (imp_congr h₁.to_iff h₂.to_iff)

Depends on / 依赖: imp_congr, propext, to_iff
-/
lemma imp_congr_eq {a b c d : Prop} (h₁ : a = c) (h₂ : b = d) : (a -> b) = (c -> d) :=
  propext (imp_congr h₁.to_iff h₂.to_iff)

/--
lemma `imp_congr_ctx_eq` / 引理 `imp_congr_ctx_eq`

English:
lemma imp_congr_ctx_eq
  given: {a b c d : Prop} (h₁ : a = c) (h₂ : c -> b = d)
  statement: (a -> b) = (c -> d)
  proof: propext (imp_congr_ctx h₁.to_iff fun hc => (h₂ hc).to_iff)

中文:
引理 imp_congr_ctx_eq
  条件: {a b c d : 命题} (h₁ : a = c) (h₂ : c -> b = d)
  结论: (a -> b) = (c -> d)
  证明: propext (imp_congr_ctx h₁.to_iff fun hc => (h₂ hc).to_iff)

Depends on / 依赖: imp_congr_ctx, propext, to_iff
-/
lemma imp_congr_ctx_eq {a b c d : Prop} (h₁ : a = c) (h₂ : c -> b = d) : (a -> b) = (c -> d) :=
  propext (imp_congr_ctx h₁.to_iff fun hc => (h₂ hc).to_iff)

/--
lemma `eq_true_intro` / 引理 `eq_true_intro`

English:
lemma eq_true_intro
  given: {a : Prop} (h : a)
  statement: a = True
  proof: propext (iff_true_intro h)

中文:
引理 eq_true_intro
  条件: {a : 命题} (h : a)
  结论: a = True
  证明: propext (iff_true_intro h)

Depends on / 依赖: iff_true_intro, propext
-/
lemma eq_true_intro {a : Prop} (h : a) : a = True := propext (iff_true_intro h)

/--
lemma `eq_false_intro` / 引理 `eq_false_intro`

English:
lemma eq_false_intro
  given: {a : Prop} (h : ¬a)
  statement: a = False
  proof: propext (iff_false_intro h)

中文:
引理 eq_false_intro
  条件: {a : 命题} (h : ¬a)
  结论: a = False
  证明: propext (iff_false_intro h)

Depends on / 依赖: iff_false_intro, propext
-/
lemma eq_false_intro {a : Prop} (h : ¬a) : a = False := propext (iff_false_intro h)

-- FIXME: `alias` creates `def Iff.eq := propext` instead of `lemma Iff.eq := propext`
alias Iff.eq := propext

/--
lemma `iff_eq_eq` / 引理 `iff_eq_eq`

English:
lemma iff_eq_eq
  given: {a b : Prop}
  statement: (a ↔ b) = (a = b)
  proof: propext ⟨propext, Eq.to_iff⟩

中文:
引理 iff_eq_eq
  条件: {a b : 命题}
  结论: (a ↔ b) = (a = b)
  证明: propext ⟨propext, Eq.to_iff⟩

Depends on / 依赖: Eq.to_iff, propext, to_iff
-/
lemma iff_eq_eq {a b : Prop} : (a ↔ b) = (a = b) := propext ⟨propext, Eq.to_iff⟩

-- They were not used in Lean 3 and there are already lemmas with those names in Lean 4

/--
theorem `forall_true_left` / 定理 `forall_true_left`

English:
theorem forall_true_left
  given: (p : True -> Prop)
  statement: (forall x, p x) ↔ p True.intro
  proof: forall_prop_of_true _

@[simp]

中文:
定理 forall_true_left
  条件: (p : True -> 命题)
  结论: (对任意 x, p x) ↔ p True.intro
  证明: forall_prop_of_true _

@[simp]
-/
@[simp] theorem forall_true_left (p : True -> Prop) : (forall x, p x) ↔ p True.intro :=
  forall_prop_of_true _

@[simp]
/--
lemma `Subsingleton.forall₂_iff` / 引理 `Subsingleton.forall₂_iff`

English:
lemma Subsingleton.forall₂_iff
  given: {ι : Sort*} [Subsingleton ι] (P : ι -> ι -> Prop)
  proof: by
  refine forall_congr' fun i => ?_
  have : Nonempty ι := ⟨i⟩
  simp [Subsingleton.elim _ i]

中文:
引理 Subsingleton.forall₂_iff
  条件: {ι : Sort*} [Subsingleton ι] (P : ι -> ι -> 命题)
  证明: by
  refine forall_congr' fun i => ?_
  have : Nonempty ι := ⟨i⟩
  simp [Subsingleton.elim _ i]

Depends on / 依赖: Nonempty, Subsingleton, Subsingleton.elim, forall_congr
-/
lemma Subsingleton.forall₂_iff {ι : Sort*} [Subsingleton ι] (P : ι -> ι -> Prop) :
    (forall i j, P i j) ↔ (forall i, P i i) := by
  refine forall_congr' fun i => ?_
  have : Nonempty ι := ⟨i⟩
  simp [Subsingleton.elim _ i]

end Quantifiers

/-! ### Classical lemmas -/

namespace Classical

-- use shortened names to avoid conflict when classical namespace is open.
/-- Any prop `p` is decidable classically. A shorthand for `Classical.propDecidable`. -/
@[instance_reducible]
/--
Definition of `dec` / `dec` 的定义

English:
definition dec
  signature: (p : Prop)
  body: by infer_instance

中文:
定义 dec
  签名: (p : 命题)
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
noncomputable def dec (p : Prop) : Decidable p := by infer_instance

variable {α : Sort*}

/-- Any predicate `p` is decidable classically. -/
@[instance_reducible]
/--
Definition of `decPred` / `decPred` 的定义

English:
definition decPred
  signature: (p : α -> Prop)
  body: by infer_instance

中文:
定义 decPred
  签名: (p : α -> 命题)
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
noncomputable def decPred (p : α -> Prop) : DecidablePred p := by infer_instance

/-- Any relation `p` is decidable classically. -/
@[instance_reducible]
/--
Definition of `decRel` / `decRel` 的定义

English:
definition decRel
  signature: (p : α -> α -> Prop)
  body: by infer_instance

中文:
定义 decRel
  签名: (p : α -> α -> 命题)
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
noncomputable def decRel (p : α -> α -> Prop) : DecidableRel p := by infer_instance

/-- Any type `α` has decidable equality classically. -/
@[instance_reducible]
/--
Definition of `decEq` / `decEq` 的定义

English:
definition decEq
  signature: (α : Sort*)
  body: by infer_instance

中文:
定义 decEq
  签名: (α : Sort*)
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
noncomputable def decEq (α : Sort*) : DecidableEq α := by infer_instance

/--
Definition of `existsCases` / `existsCases` 的定义

English:
definition existsCases
  signature: {α C : Sort*} {p : α -> Prop} (H0 : C) (H : forall a, p a -> C)
  body: if h : exists a, p a then H (Classical.choose h) (Classical.choose_spec h) else H0

中文:
定义 existsCases
  签名: {α C : Sort*} {p : α -> 命题} (H0 : C) (H : 对任意 a, p a -> C)
  定义体: if h : exists a, p a then H (Classical.choose h) (Classical.choose_spec h) else H0

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, choose_spec
-/
noncomputable def existsCases {α C : Sort*} {p : α -> Prop} (H0 : C) (H : forall a, p a -> C) : C :=
  if h : exists a, p a then H (Classical.choose h) (Classical.choose_spec h) else H0

/--
theorem `some_spec₂` / 定理 `some_spec₂`

English:
theorem some_spec₂
  statement: {α : Sort*} {p : α -> Prop} {h : exists a, p a} (q : α -> Prop)
  proof: hpq _ choose_spec _

中文:
定理 some_spec₂
  结论: {α : Sort*} {p : α -> 命题} {h : 存在 a, p a} (q : α -> 命题)
  证明: hpq _ choose_spec _

Depends on / 依赖: choose_spec
-/
theorem some_spec₂ {α : Sort*} {p : α -> Prop} {h : exists a, p a} (q : α -> Prop)
(hpq : forall a, p a -> q a) : q (choose h) := hpq _ choose_spec _

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def byContradiction' {α : Sort*} (H : ¬(α -> False))
  body: Classical.choice (peirce _ False) fun h => (H fun a => h ⟨a⟩).elim

中文:
定义 noncomputable
  签名: def byContradiction' {α : Sort*} (H : ¬(α -> False))
  定义体: Classical.choice (peirce _ False) fun h => (H fun a => h ⟨a⟩).elim
-/
protected noncomputable def byContradiction' {α : Sort*} (H : ¬(α -> False)) : α :=
Classical.choice (peirce _ False) fun h => (H fun a => h ⟨a⟩).elim

/--
Definition of `choice_of_byContradiction'` / `choice_of_byContradiction'` 的定义

English:
definition choice_of_byContradiction'
  signature: {α : Sort*} (contra : ¬(α -> False) -> α)
  body: fun H => contra H.elim

中文:
定义 choice_of_byContradiction'
  签名: {α : Sort*} (contra : ¬(α -> False) -> α)
  定义体: fun H => contra H.elim

Depends on / 依赖: H.elim, contra
-/
def choice_of_byContradiction' {α : Sort*} (contra : ¬(α -> False) -> α) : Nonempty α -> α :=
  fun H => contra H.elim

-- This can be removed after https://github.com/leanprover/lean4/pull/11316
-- arrives in a release candidate.
grind_pattern Exists.choose_spec => P.choose

/--
lemma `choose_eq` / 引理 `choose_eq`

English:
lemma choose_eq
  given: (a : α)
  statement: @Exists.choose _ (· = a) ⟨a, rfl⟩ = a
  proof: @choose_spec _ (· = a) _

@[simp]

中文:
引理 choose_eq
  条件: (a : α)
  结论: @Exists.choose _ (· = a) ⟨a, rfl⟩ = a
  证明: @choose_spec _ (· = a) _

@[simp]
-/
@[simp] lemma choose_eq (a : α) : @Exists.choose _ (· = a) ⟨a, rfl⟩ = a := @choose_spec _ (· = a) _

@[simp]
/--
lemma `choose_eq'` / 引理 `choose_eq'`

English:
lemma choose_eq'
  given: (a : α)
  statement: @Exists.choose _ (a = ·) ⟨a, rfl⟩ = a
  proof: (@choose_spec _ (a = ·) _).symm

alias axiom_of_choice := axiomOfChoice -- TODO: remove? rename in core?
alias by_cases := byCases -- TODO: remove? rename in core?
alias by_contradiction := byContradiction -- TODO: remove? rename in core?

中文:
引理 choose_eq'
  条件: (a : α)
  结论: @Exists.choose _ (a = ·) ⟨a, rfl⟩ = a
  证明: (@choose_spec _ (a = ·) _).symm

alias axiom_of_choice := axiomOfChoice -- TODO: remove? rename in core?
alias by_cases := byCases -- TODO: remove? rename in core?
alias by_contradiction := byContradiction -- TODO: remove? rename in core?

Depends on / 依赖: choose_spec
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

/--
Definition of `Exists.classicalRecOn` / `Exists.classicalRecOn` 的定义

English:
definition Exists.classicalRecOn
  signature: {α : Sort*} {p : α -> Prop} (h : exists a, p a)
  body: H (Classical.choose h) (Classical.choose_spec h)

中文:
定义 Exists.classicalRecOn
  签名: {α : Sort*} {p : α -> 命题} (h : 存在 a, p a)
  定义体: H (Classical.choose h) (Classical.choose_spec h)

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, choose_spec
-/
noncomputable def Exists.classicalRecOn {α : Sort*} {p : α -> Prop} (h : exists a, p a)
    {C : Sort*} (H : forall a, p a -> C) : C :=
  H (Classical.choose h) (Classical.choose_spec h)

/-! ### Declarations about bounded quantifiers -/
section BoundedQuantifiers

variable {α : Sort*} {r p q : α -> Prop} {P Q : forall x, p x -> Prop}

/--
theorem `bex_def` / 定理 `bex_def`

English:
theorem bex_def
  statement: (exists (x : _) (_ : p x), q x) ↔ exists x, p x ∧ q x
  proof: ⟨fun ⟨x, px, qx⟩ => ⟨x, px, qx⟩, fun ⟨x, px, qx⟩ => ⟨x, px, qx⟩⟩

中文:
定理 bex_def
  结论: (存在 (x : _) (_ : p x), q x) ↔ 存在 x, p x ∧ q x
  证明: ⟨fun ⟨x, px, qx⟩ => ⟨x, px, qx⟩, fun ⟨x, px, qx⟩ => ⟨x, px, qx⟩⟩
-/
theorem bex_def : (exists (x : _) (_ : p x), q x) ↔ exists x, p x ∧ q x :=
  ⟨fun ⟨x, px, qx⟩ => ⟨x, px, qx⟩, fun ⟨x, px, qx⟩ => ⟨x, px, qx⟩⟩

/--
theorem `BEx.elim` / 定理 `BEx.elim`

English:
theorem BEx.elim
  given: {b : Prop}
  statement: (exists x h, P x h) -> (forall a h, P a h -> b) -> b

中文:
定理 BEx.elim
  条件: {b : 命题}
  结论: (存在 x h, P x h) -> (对任意 a h, P a h -> b) -> b
-/
theorem BEx.elim {b : Prop} : (exists x h, P x h) -> (forall a h, P a h -> b) -> b
  | ⟨a, h₁, h₂⟩, h' => h' a h₁ h₂

/--
theorem `BEx.intro` / 定理 `BEx.intro`

English:
theorem BEx.intro
  given: (a : α) (h₁ : p a) (h₂ : P a h₁)
  statement: exists (x : _) (h : p x), P x h
  proof: ⟨a, h₁, h₂⟩

中文:
定理 BEx.intro
  条件: (a : α) (h₁ : p a) (h₂ : P a h₁)
  结论: 存在 (x : _) (h : p x), P x h
  证明: ⟨a, h₁, h₂⟩
-/
theorem BEx.intro (a : α) (h₁ : p a) (h₂ : P a h₁) : exists (x : _) (h : p x), P x h :=
  ⟨a, h₁, h₂⟩

/--
theorem `BAll.imp_right` / 定理 `BAll.imp_right`

English:
theorem BAll.imp_right
  given: (H : forall x h, P x h -> Q x h) (h₁ : forall x h, P x h) (x h)
  statement: Q x h
  proof: H _ _ h₁ _ _

中文:
定理 BAll.imp_right
  条件: (H : 对任意 x h, P x h -> Q x h) (h₁ : 对任意 x h, P x h) (x h)
  结论: Q x h
  证明: H _ _ h₁ _ _
-/
theorem BAll.imp_right (H : forall x h, P x h -> Q x h) (h₁ : forall x h, P x h) (x h) : Q x h :=
H _ _ h₁ _ _

/--
theorem `BEx.imp_right` / 定理 `BEx.imp_right`

English:
theorem BEx.imp_right
  given: (H : forall x h, P x h -> Q x h)
  statement: (exists x h, P x h) -> exists x h, Q x h

中文:
定理 BEx.imp_right
  条件: (H : 对任意 x h, P x h -> Q x h)
  结论: (存在 x h, P x h) -> 存在 x h, Q x h
-/
theorem BEx.imp_right (H : forall x h, P x h -> Q x h) : (exists x h, P x h) -> exists x h, Q x h
  | ⟨_, _, h'⟩ => ⟨_, _, H _ _ h'⟩

/--
theorem `BAll.imp_left` / 定理 `BAll.imp_left`

English:
theorem BAll.imp_left
  given: (H : forall x, p x -> q x) (h₁ : forall x, q x -> r x) (x) (h : p x)
  statement: r x
  proof: h₁ _ H _ h

中文:
定理 BAll.imp_left
  条件: (H : 对任意 x, p x -> q x) (h₁ : 对任意 x, q x -> r x) (x) (h : p x)
  结论: r x
  证明: h₁ _ H _ h
-/
theorem BAll.imp_left (H : forall x, p x -> q x) (h₁ : forall x, q x -> r x) (x) (h : p x) : r x :=
h₁ _ H _ h

/--
theorem `BEx.imp_left` / 定理 `BEx.imp_left`

English:
theorem BEx.imp_left
  given: (H : forall x, p x -> q x)
  statement: (exists (x : _) (_ : p x), r x) -> exists (x : _) (_ : q x), r x

中文:
定理 BEx.imp_left
  条件: (H : 对任意 x, p x -> q x)
  结论: (存在 (x : _) (_ : p x), r x) -> 存在 (x : _) (_ : q x), r x
-/
theorem BEx.imp_left (H : forall x, p x -> q x) : (exists (x : _) (_ : p x), r x) -> exists (x : _) (_ : q x), r x
  | ⟨x, hp, hr⟩ => ⟨x, H _ hp, hr⟩

/--
theorem `exists_mem_of_exists` / 定理 `exists_mem_of_exists`

English:
theorem exists_mem_of_exists
  given: (H : forall x, p x)
  statement: (exists x, q x) -> exists (x : _) (_ : p x), q x

中文:
定理 exists_mem_of_exists
  条件: (H : 对任意 x, p x)
  结论: (存在 x, q x) -> 存在 (x : _) (_ : p x), q x
-/
theorem exists_mem_of_exists (H : forall x, p x) : (exists x, q x) -> exists (x : _) (_ : p x), q x
  | ⟨x, hq⟩ => ⟨x, H x, hq⟩

/--
theorem `exists_of_exists_mem` / 定理 `exists_of_exists_mem`

English:
theorem exists_of_exists_mem
  statement: (exists (x : _) (_ : p x), q x) -> exists x, q x

中文:
定理 exists_of_exists_mem
  结论: (存在 (x : _) (_ : p x), q x) -> 存在 x, q x
-/
theorem exists_of_exists_mem : (exists (x : _) (_ : p x), q x) -> exists x, q x
  | ⟨x, _, hq⟩ => ⟨x, hq⟩


/--
theorem `not_exists_mem` / 定理 `not_exists_mem`

English:
theorem not_exists_mem
  statement: (¬exists x h, P x h) ↔ forall x h, ¬P x h
  proof: exists₂_imp

中文:
定理 not_exists_mem
  结论: (¬存在 x h, P x h) ↔ 对任意 x h, ¬P x h
  证明: exists₂_imp
-/
theorem not_exists_mem : (¬exists x h, P x h) ↔ forall x h, ¬P x h := exists₂_imp

/--
theorem `not_forall₂_of_exists₂_not` / 定理 `not_forall₂_of_exists₂_not`

English:
theorem not_forall₂_of_exists₂_not
  statement: (exists x h, ¬P x h) -> ¬forall x h, P x h

中文:
定理 not_forall₂_of_exists₂_not
  结论: (存在 x h, ¬P x h) -> ¬对任意 x h, P x h

Depends on / 依赖: Not.decidable_imp_symm, decidable_imp_symm, nx.decidable_imp_symm
-/
theorem not_forall₂_of_exists₂_not : (exists x h, ¬P x h) -> ¬forall x h, P x h
| ⟨x, h, hp⟩, al => hp al x h

-- See Note [decidable namespace]
/--
theorem `Decidable.not_forall₂` / 定理 `Decidable.not_forall₂`

English:
theorem Decidable.not_forall₂
  given: [Decidable (exists x h, ¬P x h)] [forall x h, Decidable (P x h)]
  proof: ⟨Not.decidable_imp_symm fun nx x h => nx.decidable_imp_symm
    fun h' => ⟨x, h, h'⟩, not_forall₂_of_exists₂_not⟩

中文:
定理 Decidable.not_forall₂
  条件: [Decidable (存在 x h, ¬P x h)] [对任意 x h, Decidable (P x h)]
  证明: ⟨Not.decidable_imp_symm fun nx x h => nx.decidable_imp_symm
    fun h' => ⟨x, h, h'⟩, not_forall₂_of_exists₂_not⟩
-/
protected theorem Decidable.not_forall₂ [Decidable (exists x h, ¬P x h)] [forall x h, Decidable (P x h)] :
    (¬forall x h, P x h) ↔ exists x h, ¬P x h :=
  ⟨Not.decidable_imp_symm fun nx x h => nx.decidable_imp_symm
    fun h' => ⟨x, h, h'⟩, not_forall₂_of_exists₂_not⟩

/--
theorem `not_forall₂` / 定理 `not_forall₂`

English:
theorem not_forall₂
  statement: (¬forall x h, P x h) ↔ exists x h, ¬P x h
  proof: open scoped Classical in Decidable.not_forall₂

中文:
定理 not_forall₂
  结论: (¬对任意 x h, P x h) ↔ 存在 x h, ¬P x h
  证明: open scoped Classical in Decidable.not_forall₂

Depends on / 依赖: Classical, Decidable, Decidable.not_forall, scoped
-/
theorem not_forall₂ : (¬forall x h, P x h) ↔ exists x h, ¬P x h :=
  open scoped Classical in Decidable.not_forall₂

/--
theorem `forall₂_and` / 定理 `forall₂_and`

English:
theorem forall₂_and
  statement: (forall x h, P x h ∧ Q x h) ↔ (forall x h, P x h) ∧ forall x h, Q x h
  proof: Iff.trans (forall_congr' fun _ => forall_and) forall_and

中文:
定理 forall₂_and
  结论: (对任意 x h, P x h ∧ Q x h) ↔ (对任意 x h, P x h) ∧ 对任意 x h, Q x h
  证明: Iff.trans (forall_congr' fun _ => forall_and) forall_and

Depends on / 依赖: Iff.trans, forall_and, forall_congr
-/
theorem forall₂_and : (forall x h, P x h ∧ Q x h) ↔ (forall x h, P x h) ∧ forall x h, Q x h :=
  Iff.trans (forall_congr' fun _ => forall_and) forall_and

/--
theorem `forall_and_left` / 定理 `forall_and_left`

English:
theorem forall_and_left
  given: [Nonempty α] (q : Prop) (p : α -> Prop)
  proof: by rw [forall_and, forall_const]

中文:
定理 forall_and_left
  条件: [Nonempty α] (q : 命题) (p : α -> 命题)
  证明: by rw [forall_and, forall_const]

Depends on / 依赖: forall_and, forall_const
-/
theorem forall_and_left [Nonempty α] (q : Prop) (p : α -> Prop) :
    (forall x, q ∧ p x) ↔ (q ∧ forall x, p x) := by rw [forall_and, forall_const]

/--
theorem `forall_and_right` / 定理 `forall_and_right`

English:
theorem forall_and_right
  given: [Nonempty α] (p : α -> Prop) (q : Prop)
  proof: by rw [forall_and, forall_const]

中文:
定理 forall_and_right
  条件: [Nonempty α] (p : α -> 命题) (q : 命题)
  证明: by rw [forall_and, forall_const]

Depends on / 依赖: forall_and, forall_const
-/
theorem forall_and_right [Nonempty α] (p : α -> Prop) (q : Prop) :
    (forall x, p x ∧ q) ↔ (forall x, p x) ∧ q := by rw [forall_and, forall_const]

/--
theorem `exists_mem_or` / 定理 `exists_mem_or`

English:
theorem exists_mem_or
  statement: (exists x h, P x h ∨ Q x h) ↔ (exists x h, P x h) ∨ exists x h, Q x h
  proof: Iff.trans (exists_congr fun _ => exists_or) exists_or

中文:
定理 exists_mem_or
  结论: (存在 x h, P x h ∨ Q x h) ↔ (存在 x h, P x h) ∨ 存在 x h, Q x h
  证明: Iff.trans (exists_congr fun _ => exists_or) exists_or

Depends on / 依赖: Iff.trans, exists_congr, exists_or
-/
theorem exists_mem_or : (exists x h, P x h ∨ Q x h) ↔ (exists x h, P x h) ∨ exists x h, Q x h :=
  Iff.trans (exists_congr fun _ => exists_or) exists_or

/--
theorem `forall₂_or_left` / 定理 `forall₂_or_left`

English:
theorem forall₂_or_left
  statement: (forall x, p x ∨ q x -> r x) ↔ (forall x, p x -> r x) ∧ forall x, q x -> r x
  proof: Iff.trans (forall_congr' fun _ => or_imp) forall_and

中文:
定理 forall₂_or_left
  结论: (对任意 x, p x ∨ q x -> r x) ↔ (对任意 x, p x -> r x) ∧ 对任意 x, q x -> r x
  证明: Iff.trans (forall_congr' fun _ => or_imp) forall_and

Depends on / 依赖: Iff.trans, forall_and, forall_congr, or_imp
-/
theorem forall₂_or_left : (forall x, p x ∨ q x -> r x) ↔ (forall x, p x -> r x) ∧ forall x, q x -> r x :=
  Iff.trans (forall_congr' fun _ => or_imp) forall_and

/--
theorem `exists_mem_or_left` / 定理 `exists_mem_or_left`

English:
theorem exists_mem_or_left
  proof: by
  simp only [exists_prop]
  exact Iff.trans (exists_congr fun x => or_and_right) exists_or

中文:
定理 exists_mem_or_left
  证明: by
  simp only [exists_prop]
  exact Iff.trans (exists_congr fun x => or_and_right) exists_or

Depends on / 依赖: Iff.trans, exists_congr, exists_or, exists_prop, or_and_right
-/
theorem exists_mem_or_left :
    (exists (x : _) (_ : p x ∨ q x), r x) ↔ (exists (x : _) (_ : p x), r x) ∨ exists (x : _) (_ : q x), r x := by
  simp only [exists_prop]
  exact Iff.trans (exists_congr fun x => or_and_right) exists_or

end BoundedQuantifiers

section ite

variable {α : Sort*} {σ : α -> Sort*} {P Q R : Prop} [Decidable P]
  {a b c : α} {A : P -> α} {B : ¬P -> α}

/--
theorem `dite_eq_iff` / 定理 `dite_eq_iff`

English:
theorem dite_eq_iff
  statement: dite P A B = c ↔ (exists h, A h = c) ∨ exists h, B h = c
  proof: by
  by_cases P <;> simp [*, exists_prop_of_true, exists_prop_of_false]

中文:
定理 dite_eq_iff
  结论: dite P A B = c ↔ (存在 h, A h = c) ∨ 存在 h, B h = c
  证明: by
  by_cases P <;> simp [*, exists_prop_of_true, exists_prop_of_false]

Depends on / 依赖: exists_prop_of_false, exists_prop_of_true
-/
theorem dite_eq_iff : dite P A B = c ↔ (exists h, A h = c) ∨ exists h, B h = c := by
  by_cases P <;> simp [*, exists_prop_of_true, exists_prop_of_false]

/--
theorem `ite_eq_iff` / 定理 `ite_eq_iff`

English:
theorem ite_eq_iff
  statement: ite P a b = c ↔ P ∧ a = c ∨ ¬P ∧ b = c
  proof: dite_eq_iff.trans by rw [exists_prop, exists_prop]

中文:
定理 ite_eq_iff
  结论: ite P a b = c ↔ P ∧ a = c ∨ ¬P ∧ b = c
  证明: dite_eq_iff.trans by rw [exists_prop, exists_prop]

Depends on / 依赖: dite_eq_iff, dite_eq_iff.trans, exists_prop
-/
theorem ite_eq_iff : ite P a b = c ↔ P ∧ a = c ∨ ¬P ∧ b = c :=
dite_eq_iff.trans by rw [exists_prop, exists_prop]

/--
theorem `eq_ite_iff` / 定理 `eq_ite_iff`

English:
theorem eq_ite_iff
  statement: a = ite P b c ↔ P ∧ a = b ∨ ¬P ∧ a = c
  proof: eq_comm.trans ite_eq_iff.trans (Iff.rfl.and eq_comm).or (Iff.rfl.and eq_comm)

中文:
定理 eq_ite_iff
  结论: a = ite P b c ↔ P ∧ a = b ∨ ¬P ∧ a = c
  证明: eq_comm.trans ite_eq_iff.trans (Iff.rfl.and eq_comm).or (Iff.rfl.and eq_comm)

Depends on / 依赖: Iff.rfl.and, eq_comm, eq_comm.trans, ite_eq_iff, ite_eq_iff.trans
-/
theorem eq_ite_iff : a = ite P b c ↔ P ∧ a = b ∨ ¬P ∧ a = c :=
eq_comm.trans ite_eq_iff.trans (Iff.rfl.and eq_comm).or (Iff.rfl.and eq_comm)

/--
theorem `dite_eq_iff'` / 定理 `dite_eq_iff'`

English:
theorem dite_eq_iff'
  statement: dite P A B = c ↔ (forall h, A h = c) ∧ forall h, B h = c
  proof: ⟨fun he => ⟨fun h => (dif_pos h).symm.trans he, fun h => (dif_neg h).symm.trans he⟩, fun he =>
(em P).elim (fun h => (dif_pos h).trans <| he.1 h) fun h => (dif_neg h).trans he.2 h⟩

中文:
定理 dite_eq_iff'
  结论: dite P A B = c ↔ (对任意 h, A h = c) ∧ 对任意 h, B h = c
  证明: ⟨fun he => ⟨fun h => (dif_pos h).symm.trans he, fun h => (dif_neg h).symm.trans he⟩, fun he =>
(em P).elim (fun h => (dif_pos h).trans <| he.1 h) fun h => (dif_neg h).trans he.2 h⟩

Depends on / 依赖: dif_neg, dif_pos, symm.trans
-/
theorem dite_eq_iff' : dite P A B = c ↔ (forall h, A h = c) ∧ forall h, B h = c :=
  ⟨fun he => ⟨fun h => (dif_pos h).symm.trans he, fun h => (dif_neg h).symm.trans he⟩, fun he =>
(em P).elim (fun h => (dif_pos h).trans <| he.1 h) fun h => (dif_neg h).trans he.2 h⟩

/--
theorem `ite_eq_iff'` / 定理 `ite_eq_iff'`

English:
theorem ite_eq_iff'
  statement: ite P a b = c ↔ (P -> a = c) ∧ (¬P -> b = c)
  proof: dite_eq_iff'

中文:
定理 ite_eq_iff'
  结论: ite P a b = c ↔ (P -> a = c) ∧ (¬P -> b = c)
  证明: dite_eq_iff'

Depends on / 依赖: dite_eq_iff
-/
theorem ite_eq_iff' : ite P a b = c ↔ (P -> a = c) ∧ (¬P -> b = c) := dite_eq_iff'

/--
theorem `dite_ne_left_iff` / 定理 `dite_ne_left_iff`

English:
theorem dite_ne_left_iff
  statement: dite P (fun _ => a) B != a ↔ exists h, a != B h
  proof: by
  grind

中文:
定理 dite_ne_left_iff
  结论: dite P (fun _ => a) B != a ↔ 存在 h, a != B h
  证明: by
  grind
-/
theorem dite_ne_left_iff : dite P (fun _ => a) B != a ↔ exists h, a != B h := by
  grind

/--
theorem `dite_ne_right_iff` / 定理 `dite_ne_right_iff`

English:
theorem dite_ne_right_iff
  statement: (dite P A fun _ => b) != b ↔ exists h, A h != b
  proof: by
  simp only [Ne, dite_eq_right_iff, not_forall]

中文:
定理 dite_ne_right_iff
  结论: (dite P A fun _ => b) != b ↔ 存在 h, A h != b
  证明: by
  simp only [Ne, dite_eq_right_iff, not_forall]

Depends on / 依赖: dite_eq_right_iff, not_forall
-/
theorem dite_ne_right_iff : (dite P A fun _ => b) != b ↔ exists h, A h != b := by
  simp only [Ne, dite_eq_right_iff, not_forall]

/--
theorem `ite_ne_left_iff` / 定理 `ite_ne_left_iff`

English:
theorem ite_ne_left_iff
  statement: ite P a b != a ↔ ¬P ∧ a != b
  proof: dite_ne_left_iff.trans by rw [exists_prop]

中文:
定理 ite_ne_left_iff
  结论: ite P a b != a ↔ ¬P ∧ a != b
  证明: dite_ne_left_iff.trans by rw [exists_prop]

Depends on / 依赖: dite_ne_left_iff, dite_ne_left_iff.trans, exists_prop
-/
theorem ite_ne_left_iff : ite P a b != a ↔ ¬P ∧ a != b :=
dite_ne_left_iff.trans by rw [exists_prop]

/--
theorem `ite_ne_right_iff` / 定理 `ite_ne_right_iff`

English:
theorem ite_ne_right_iff
  statement: ite P a b != b ↔ P ∧ a != b
  proof: dite_ne_right_iff.trans by rw [exists_prop]

中文:
定理 ite_ne_right_iff
  结论: ite P a b != b ↔ P ∧ a != b
  证明: dite_ne_right_iff.trans by rw [exists_prop]

Depends on / 依赖: dite_ne_right_iff, dite_ne_right_iff.trans, exists_prop
-/
theorem ite_ne_right_iff : ite P a b != b ↔ P ∧ a != b :=
dite_ne_right_iff.trans by rw [exists_prop]

/--
theorem `Ne.dite_eq_left_iff` / 定理 `Ne.dite_eq_left_iff`

English:
theorem Ne.dite_eq_left_iff
  given: (h : forall h, a != B h)
  statement: dite P (fun _ => a) B = a ↔ P
  proof: dite_eq_left_iff.trans ⟨fun H => of_not_not fun h' => h h' (H h').symm, fun h H => (H h).elim⟩

中文:
定理 Ne.dite_eq_left_iff
  条件: (h : 对任意 h, a != B h)
  结论: dite P (fun _ => a) B = a ↔ P
  证明: dite_eq_left_iff.trans ⟨fun H => of_not_not fun h' => h h' (H h').symm, fun h H => (H h).elim⟩
-/
protected theorem Ne.dite_eq_left_iff (h : forall h, a != B h) : dite P (fun _ => a) B = a ↔ P :=
  dite_eq_left_iff.trans ⟨fun H => of_not_not fun h' => h h' (H h').symm, fun h H => (H h).elim⟩

/--
theorem `Ne.dite_eq_right_iff` / 定理 `Ne.dite_eq_right_iff`

English:
theorem Ne.dite_eq_right_iff
  given: (h : forall h, A h != b)
  statement: (dite P A fun _ => b) = b ↔ ¬P
  proof: dite_eq_right_iff.trans ⟨fun H h' => h h' (H h'), fun h' H => (h' H).elim⟩

中文:
定理 Ne.dite_eq_right_iff
  条件: (h : 对任意 h, A h != b)
  结论: (dite P A fun _ => b) = b ↔ ¬P
  证明: dite_eq_right_iff.trans ⟨fun H h' => h h' (H h'), fun h' H => (h' H).elim⟩
-/
protected theorem Ne.dite_eq_right_iff (h : forall h, A h != b) : (dite P A fun _ => b) = b ↔ ¬P :=
  dite_eq_right_iff.trans ⟨fun H h' => h h' (H h'), fun h' H => (h' H).elim⟩

/--
theorem `Ne.ite_eq_left_iff` / 定理 `Ne.ite_eq_left_iff`

English:
theorem Ne.ite_eq_left_iff
  given: (h : a != b)
  statement: ite P a b = a ↔ P
  proof: Ne.dite_eq_left_iff fun _ => h

中文:
定理 Ne.ite_eq_left_iff
  条件: (h : a != b)
  结论: ite P a b = a ↔ P
  证明: Ne.dite_eq_left_iff fun _ => h
-/
protected theorem Ne.ite_eq_left_iff (h : a != b) : ite P a b = a ↔ P :=
  Ne.dite_eq_left_iff fun _ => h

/--
theorem `Ne.ite_eq_right_iff` / 定理 `Ne.ite_eq_right_iff`

English:
theorem Ne.ite_eq_right_iff
  given: (h : a != b)
  statement: ite P a b = b ↔ ¬P
  proof: Ne.dite_eq_right_iff fun _ => h

中文:
定理 Ne.ite_eq_right_iff
  条件: (h : a != b)
  结论: ite P a b = b ↔ ¬P
  证明: Ne.dite_eq_right_iff fun _ => h
-/
protected theorem Ne.ite_eq_right_iff (h : a != b) : ite P a b = b ↔ ¬P :=
  Ne.dite_eq_right_iff fun _ => h

/--
theorem `Ne.dite_ne_left_iff` / 定理 `Ne.dite_ne_left_iff`

English:
theorem Ne.dite_ne_left_iff
  given: (h : forall h, a != B h)
  statement: dite P (fun _ => a) B != a ↔ ¬P
  proof: dite_ne_left_iff.trans exists_iff_of_forall h

中文:
定理 Ne.dite_ne_left_iff
  条件: (h : 对任意 h, a != B h)
  结论: dite P (fun _ => a) B != a ↔ ¬P
  证明: dite_ne_left_iff.trans exists_iff_of_forall h
-/
protected theorem Ne.dite_ne_left_iff (h : forall h, a != B h) : dite P (fun _ => a) B != a ↔ ¬P :=
dite_ne_left_iff.trans exists_iff_of_forall h

/--
theorem `Ne.dite_ne_right_iff` / 定理 `Ne.dite_ne_right_iff`

English:
theorem Ne.dite_ne_right_iff
  given: (h : forall h, A h != b)
  statement: (dite P A fun _ => b) != b ↔ P
  proof: dite_ne_right_iff.trans exists_iff_of_forall h

中文:
定理 Ne.dite_ne_right_iff
  条件: (h : 对任意 h, A h != b)
  结论: (dite P A fun _ => b) != b ↔ P
  证明: dite_ne_right_iff.trans exists_iff_of_forall h
-/
protected theorem Ne.dite_ne_right_iff (h : forall h, A h != b) : (dite P A fun _ => b) != b ↔ P :=
dite_ne_right_iff.trans exists_iff_of_forall h

/--
theorem `Ne.ite_ne_left_iff` / 定理 `Ne.ite_ne_left_iff`

English:
theorem Ne.ite_ne_left_iff
  given: (h : a != b)
  statement: ite P a b != a ↔ ¬P
  proof: Ne.dite_ne_left_iff fun _ => h

中文:
定理 Ne.ite_ne_left_iff
  条件: (h : a != b)
  结论: ite P a b != a ↔ ¬P
  证明: Ne.dite_ne_left_iff fun _ => h
-/
protected theorem Ne.ite_ne_left_iff (h : a != b) : ite P a b != a ↔ ¬P :=
  Ne.dite_ne_left_iff fun _ => h

/--
theorem `Ne.ite_ne_right_iff` / 定理 `Ne.ite_ne_right_iff`

English:
theorem Ne.ite_ne_right_iff
  given: (h : a != b)
  statement: ite P a b != b ↔ P
  proof: Ne.dite_ne_right_iff fun _ => h

中文:
定理 Ne.ite_ne_right_iff
  条件: (h : a != b)
  结论: ite P a b != b ↔ P
  证明: Ne.dite_ne_right_iff fun _ => h
-/
protected theorem Ne.ite_ne_right_iff (h : a != b) : ite P a b != b ↔ P :=
  Ne.dite_ne_right_iff fun _ => h

variable (P Q a b)

/--
theorem `dite_eq_or_eq` / 定理 `dite_eq_or_eq`

English:
theorem dite_eq_or_eq
  statement: (exists h, dite P A B = A h) ∨ exists h, dite P A B = B h
  proof: if h : _ then .inl ⟨h, dif_pos h⟩ else .inr ⟨h, dif_neg h⟩

中文:
定理 dite_eq_or_eq
  结论: (存在 h, dite P A B = A h) ∨ 存在 h, dite P A B = B h
  证明: if h : _ then .inl ⟨h, dif_pos h⟩ else .inr ⟨h, dif_neg h⟩

Depends on / 依赖: dif_neg, dif_pos
-/
theorem dite_eq_or_eq : (exists h, dite P A B = A h) ∨ exists h, dite P A B = B h :=
  if h : _ then .inl ⟨h, dif_pos h⟩ else .inr ⟨h, dif_neg h⟩

/--
theorem `ite_eq_or_eq` / 定理 `ite_eq_or_eq`

English:
theorem ite_eq_or_eq
  statement: ite P a b = a ∨ ite P a b = b
  proof: if h : _ then .inl (if_pos h) else .inr (if_neg h)

中文:
定理 ite_eq_or_eq
  结论: ite P a b = a ∨ ite P a b = b
  证明: if h : _ then .inl (if_pos h) else .inr (if_neg h)

Depends on / 依赖: if_neg, if_pos
-/
theorem ite_eq_or_eq : ite P a b = a ∨ ite P a b = b :=
  if h : _ then .inl (if_pos h) else .inr (if_neg h)

/--
theorem `apply_dite₂` / 定理 `apply_dite₂`

English:
theorem apply_dite₂
  statement: {α β γ : Sort*} (f : α -> β -> γ) (P : Prop) [Decidable P]
  proof: by
  by_cases h : P <;> simp [h]

中文:
定理 apply_dite₂
  结论: {α β γ : Sort*} (f : α -> β -> γ) (P : 命题) [Decidable P]
  证明: by
  by_cases h : P <;> simp [h]
-/
theorem apply_dite₂ {α β γ : Sort*} (f : α -> β -> γ) (P : Prop) [Decidable P]
    (a : P -> α) (b : ¬P -> α) (c : P -> β) (d : ¬P -> β) :
    f (dite P a b) (dite P c d) = dite P (fun h => f (a h) (c h)) fun h => f (b h) (d h) := by
  by_cases h : P <;> simp [h]

/--
theorem `apply_ite₂` / 定理 `apply_ite₂`

English:
theorem apply_ite₂
  given: {α β γ : Sort*} (f : α -> β -> γ) (P : Prop) [Decidable P] (a b : α) (c d : β)
  proof: apply_dite₂ f P (fun _ => a) (fun _ => b) (fun _ => c) fun _ => d

中文:
定理 apply_ite₂
  条件: {α β γ : Sort*} (f : α -> β -> γ) (P : 命题) [Decidable P] (a b : α) (c d : β)
  证明: apply_dite₂ f P (fun _ => a) (fun _ => b) (fun _ => c) fun _ => d
-/
theorem apply_ite₂ {α β γ : Sort*} (f : α -> β -> γ) (P : Prop) [Decidable P] (a b : α) (c d : β) :
    f (ite P a b) (ite P c d) = ite P (f a c) (f b d) :=
  apply_dite₂ f P (fun _ => a) (fun _ => b) (fun _ => c) fun _ => d

/--
theorem `dite_apply` / 定理 `dite_apply`

English:
theorem dite_apply
  given: (f : P -> forall a, σ a) (g : ¬P -> forall a, σ a) (a : α)
  proof: by by_cases h : P <;> simp [h]

中文:
定理 dite_apply
  条件: (f : P -> 对任意 a, σ a) (g : ¬P -> 对任意 a, σ a) (a : α)
  证明: by by_cases h : P <;> simp [h]
-/
theorem dite_apply (f : P -> forall a, σ a) (g : ¬P -> forall a, σ a) (a : α) :
    (dite P f g) a = dite P (fun h => f h a) fun h => g h a := by by_cases h : P <;> simp [h]

/--
theorem `ite_apply` / 定理 `ite_apply`

English:
theorem ite_apply
  given: (f g : forall a, σ a) (a : α)
  statement: (ite P f g) a = ite P (f a) (g a)
  proof: dite_apply P (fun _ => f) (fun _ => g) a

中文:
定理 ite_apply
  条件: (f g : 对任意 a, σ a) (a : α)
  结论: (ite P f g) a = ite P (f a) (g a)
  证明: dite_apply P (fun _ => f) (fun _ => g) a

Depends on / 依赖: dite_apply
-/
theorem ite_apply (f g : forall a, σ a) (a : α) : (ite P f g) a = ite P (f a) (g a) :=
  dite_apply P (fun _ => f) (fun _ => g) a

/--
theorem `apply_ite_left` / 定理 `apply_ite_left`

English:
theorem apply_ite_left
  statement: {α β γ : Sort*} (f : α -> β -> γ) (P : Prop) [Decidable P]
  proof: by grind

中文:
定理 apply_ite_left
  结论: {α β γ : Sort*} (f : α -> β -> γ) (P : 命题) [Decidable P]
  证明: by grind
-/
theorem apply_ite_left {α β γ : Sort*} (f : α -> β -> γ) (P : Prop) [Decidable P]
    (x y : α) (z : β) : f (if P then x else y) z = if P then f x z else f y z := by grind

section
variable [Decidable Q]

/--
theorem `ite_and` / 定理 `ite_and`

English:
theorem ite_and
  statement: ite (P ∧ Q) a b = ite P (ite Q a b) b
  proof: by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]

中文:
定理 ite_and
  结论: ite (P ∧ Q) a b = ite P (ite Q a b) b
  证明: by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]
-/
theorem ite_and : ite (P ∧ Q) a b = ite P (ite Q a b) b := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]

/--
theorem `ite_or` / 定理 `ite_or`

English:
theorem ite_or
  statement: ite (P ∨ Q) a b = ite P a (ite Q a b)
  proof: by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]

中文:
定理 ite_or
  结论: ite (P ∨ Q) a b = ite P a (ite Q a b)
  证明: by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]
-/
theorem ite_or : ite (P ∨ Q) a b = ite P a (ite Q a b) := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]

/--
theorem `dite_dite_comm` / 定理 `dite_dite_comm`

English:
theorem dite_dite_comm
  given: {B : Q -> α} {C : ¬P -> ¬Q -> α} (h : P -> ¬Q)
  proof: by
  grind

中文:
定理 dite_dite_comm
  条件: {B : Q -> α} {C : ¬P -> ¬Q -> α} (h : P -> ¬Q)
  证明: by
  grind
-/
theorem dite_dite_comm {B : Q -> α} {C : ¬P -> ¬Q -> α} (h : P -> ¬Q) :
    (if p : P then A p else if q : Q then B q else C p q) =
     if q : Q then B q else if p : P then A p else C p q := by
  grind

/--
theorem `ite_ite_comm` / 定理 `ite_ite_comm`

English:
theorem ite_ite_comm
  given: (h : P -> ¬Q)
  proof: dite_dite_comm P Q h

中文:
定理 ite_ite_comm
  条件: (h : P -> ¬Q)
  证明: dite_dite_comm P Q h

Depends on / 依赖: dite_dite_comm
-/
theorem ite_ite_comm (h : P -> ¬Q) :
    (if P then a else if Q then b else c) =
     if Q then b else if P then a else c :=
  dite_dite_comm P Q h

end

variable {P Q}

/--
theorem `ite_prop_iff_or` / 定理 `ite_prop_iff_or`

English:
theorem ite_prop_iff_or
  statement: (if P then Q else R) ↔ (P ∧ Q ∨ ¬P ∧ R)
  proof: by
  by_cases p : P <;> simp [p]

中文:
定理 ite_prop_iff_or
  结论: (if P then Q else R) ↔ (P ∧ Q ∨ ¬P ∧ R)
  证明: by
  by_cases p : P <;> simp [p]
-/
theorem ite_prop_iff_or : (if P then Q else R) ↔ (P ∧ Q ∨ ¬P ∧ R) := by
  by_cases p : P <;> simp [p]

/--
theorem `dite_prop_iff_or` / 定理 `dite_prop_iff_or`

English:
theorem dite_prop_iff_or
  given: {Q : P -> Prop} {R : ¬P -> Prop}
  proof: by
  by_cases h : P <;> simp [h, exists_prop_of_false, exists_prop_of_true]

中文:
定理 dite_prop_iff_or
  条件: {Q : P -> 命题} {R : ¬P -> 命题}
  证明: by
  by_cases h : P <;> simp [h, exists_prop_of_false, exists_prop_of_true]

Depends on / 依赖: exists_prop_of_false, exists_prop_of_true
-/
theorem dite_prop_iff_or {Q : P -> Prop} {R : ¬P -> Prop} :
    dite P Q R ↔ (exists p, Q p) ∨ (exists p, R p) := by
  by_cases h : P <;> simp [h, exists_prop_of_false, exists_prop_of_true]

-- TODO make this a simp lemma in a future PR
/--
theorem `ite_prop_iff_and` / 定理 `ite_prop_iff_and`

English:
theorem ite_prop_iff_and
  statement: (if P then Q else R) ↔ ((P -> Q) ∧ (¬P -> R))
  proof: by
  by_cases p : P <;> simp [p]

中文:
定理 ite_prop_iff_and
  结论: (if P then Q else R) ↔ ((P -> Q) ∧ (¬P -> R))
  证明: by
  by_cases p : P <;> simp [p]
-/
theorem ite_prop_iff_and : (if P then Q else R) ↔ ((P -> Q) ∧ (¬P -> R)) := by
  by_cases p : P <;> simp [p]

/--
theorem `dite_prop_iff_and` / 定理 `dite_prop_iff_and`

English:
theorem dite_prop_iff_and
  given: {Q : P -> Prop} {R : ¬P -> Prop}
  proof: by
  by_cases h : P <;> simp [h, forall_prop_of_false, forall_prop_of_true]

中文:
定理 dite_prop_iff_and
  条件: {Q : P -> 命题} {R : ¬P -> 命题}
  证明: by
  by_cases h : P <;> simp [h, forall_prop_of_false, forall_prop_of_true]

Depends on / 依赖: forall_prop_of_false, forall_prop_of_true
-/
theorem dite_prop_iff_and {Q : P -> Prop} {R : ¬P -> Prop} :
    dite P Q R ↔ (forall h, Q h) ∧ (forall h, R h) := by
  by_cases h : P <;> simp [h, forall_prop_of_false, forall_prop_of_true]

section congr

variable [Decidable Q] {x y u v : α}

/--
theorem `if_ctx_congr` / 定理 `if_ctx_congr`

English:
theorem if_ctx_congr
  given: (h_c : P ↔ Q) (h_t : Q -> x = u) (h_e : ¬Q -> y = v)
  statement: ite P x y = ite Q u v
  proof: ite_congr h_c.eq h_t h_e

中文:
定理 if_ctx_congr
  条件: (h_c : P ↔ Q) (h_t : Q -> x = u) (h_e : ¬Q -> y = v)
  结论: ite P x y = ite Q u v
  证明: ite_congr h_c.eq h_t h_e

Depends on / 依赖: h_c.eq, ite_congr
-/
theorem if_ctx_congr (h_c : P ↔ Q) (h_t : Q -> x = u) (h_e : ¬Q -> y = v) : ite P x y = ite Q u v :=
  ite_congr h_c.eq h_t h_e

/--
theorem `if_congr` / 定理 `if_congr`

English:
theorem if_congr
  given: (h_c : P ↔ Q) (h_t : x = u) (h_e : y = v)
  statement: ite P x y = ite Q u v
  proof: if_ctx_congr h_c (fun _ => h_t) (fun _ => h_e)

中文:
定理 if_congr
  条件: (h_c : P ↔ Q) (h_t : x = u) (h_e : y = v)
  结论: ite P x y = ite Q u v
  证明: if_ctx_congr h_c (fun _ => h_t) (fun _ => h_e)

Depends on / 依赖: if_ctx_congr
-/
theorem if_congr (h_c : P ↔ Q) (h_t : x = u) (h_e : y = v) : ite P x y = ite Q u v :=
  if_ctx_congr h_c (fun _ => h_t) (fun _ => h_e)

end congr

/--
theorem `Function.Injective.ite` / 定理 `Function.Injective.ite`

English:
theorem Function.Injective.ite
  statement: {α β : Sort*} {p : β -> Prop} [DecidablePred p] {g : β -> α}
  proof: fun x y _ => by rcases em (p x) with (hx | hx) <;> rcases em (p y) with (hy | hy) <;> grind

中文:
定理 Function.Injective.ite
  结论: {α β : Sort*} {p : β -> 命题} [DecidablePred p] {g : β -> α}
  证明: fun x y _ => by rcases em (p x) with (hx | hx) <;> rcases em (p y) with (hy | hy) <;> grind
-/
theorem Function.Injective.ite {α β : Sort*} {p : β -> Prop} [DecidablePred p] {g : β -> α}
    (hg : g.Injective) {f : β -> α} (hf : f.Injective) (h : forall x y, g x = f y -> x = y) :
    (fun x => if p x then g x else f x).Injective :=
  fun x y _ => by rcases em (p x) with (hx | hx) <;> rcases em (p y) with (hy | hy) <;> grind

end ite

/-! ### Membership -/

alias Membership.mem.ne_of_notMem := ne_of_mem_of_not_mem
alias Membership.mem.ne_of_notMem' := ne_of_mem_of_not_mem'

section Membership

variable {α β : Type*} [Membership α β] {p : Prop} [Decidable p]

/--
theorem `mem_dite` / 定理 `mem_dite`

English:
theorem mem_dite
  given: {a : α} {s : p -> β} {t : ¬p -> β}
  proof: by
  by_cases h : p <;> simp [h]

中文:
定理 mem_dite
  条件: {a : α} {s : p -> β} {t : ¬p -> β}
  证明: by
  by_cases h : p <;> simp [h]
-/
theorem mem_dite {a : α} {s : p -> β} {t : ¬p -> β} :
    (a in if h : p then s h else t h) ↔ (forall h, a in s h) ∧ (forall h, a in t h) := by
  by_cases h : p <;> simp [h]

/--
theorem `dite_mem` / 定理 `dite_mem`

English:
theorem dite_mem
  given: {a : p -> α} {b : ¬p -> α} {s : β}
  proof: by
  by_cases h : p <;> simp [h]

中文:
定理 dite_mem
  条件: {a : p -> α} {b : ¬p -> α} {s : β}
  证明: by
  by_cases h : p <;> simp [h]
-/
theorem dite_mem {a : p -> α} {b : ¬p -> α} {s : β} :
    (if h : p then a h else b h) in s ↔ (forall h, a h in s) ∧ (forall h, b h in s) := by
  by_cases h : p <;> simp [h]

/--
theorem `mem_ite` / 定理 `mem_ite`

English:
theorem mem_ite
  given: {a : α} {s t : β}
  statement: (a in if p then s else t) ↔ (p -> a in s) ∧ (¬p -> a in t)
  proof: mem_dite

中文:
定理 mem_ite
  条件: {a : α} {s t : β}
  结论: (a in if p then s else t) ↔ (p -> a in s) ∧ (¬p -> a in t)
  证明: mem_dite

Depends on / 依赖: mem_dite
-/
theorem mem_ite {a : α} {s t : β} : (a in if p then s else t) ↔ (p -> a in s) ∧ (¬p -> a in t) :=
  mem_dite

/--
theorem `ite_mem` / 定理 `ite_mem`

English:
theorem ite_mem
  given: {a b : α} {s : β}
  statement: (if p then a else b) in s ↔ (p -> a in s) ∧ (¬p -> b in s)
  proof: dite_mem

中文:
定理 ite_mem
  条件: {a b : α} {s : β}
  结论: (if p then a else b) in s ↔ (p -> a in s) ∧ (¬p -> b in s)
  证明: dite_mem

Depends on / 依赖: dite_mem
-/
theorem ite_mem {a b : α} {s : β} : (if p then a else b) in s ↔ (p -> a in s) ∧ (¬p -> b in s) :=
  dite_mem

end Membership

/--
theorem `not_beq_of_ne` / 定理 `not_beq_of_ne`

English:
theorem not_beq_of_ne
  given: {α : Type*} [BEq α] [LawfulBEq α] {a b : α} (ne : a != b)
  statement: ¬(a == b)
  proof: fun h => ne (eq_of_beq h)

alias beq_eq_decide := Bool.beq_eq_decide_eq

中文:
定理 not_beq_of_ne
  条件: {α : 类型} [BEq α] [LawfulBEq α] {a b : α} (ne : a != b)
  结论: ¬(a == b)
  证明: fun h => ne (eq_of_beq h)

alias beq_eq_decide := Bool.beq_eq_decide_eq

Depends on / 依赖: eq_of_beq
-/
theorem not_beq_of_ne {α : Type*} [BEq α] [LawfulBEq α] {a b : α} (ne : a != b) : ¬(a == b) :=
  fun h => ne (eq_of_beq h)

alias beq_eq_decide := Bool.beq_eq_decide_eq

/--
lemma `beq_eq_beq` / 引理 `beq_eq_beq`

English:
lemma beq_eq_beq
  statement: {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {a₁ a₂ : α}
  proof: by rw [Bool.eq_iff_iff]; simp

@[ext]

中文:
引理 beq_eq_beq
  结论: {α β : 类型} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {a₁ a₂ : α}
  证明: by rw [Bool.eq_iff_iff]; simp

@[ext]
-/
@[simp] lemma beq_eq_beq {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {a₁ a₂ : α}
    {b₁ b₂ : β} : (a₁ == a₂) = (b₁ == b₂) ↔ (a₁ = a₂ ↔ b₁ = b₂) := by rw [Bool.eq_iff_iff]; simp

@[ext]
/--
theorem `beq_ext` / 定理 `beq_ext`

English:
theorem beq_ext
  statement: {α : Type*} (inst1 : BEq α) (inst2 : BEq α)
  proof: by
  have ⟨beq1⟩ := inst1
  congr
  funext x y
  exact h x y

中文:
定理 beq_ext
  结论: {α : 类型} (inst1 : BEq α) (inst2 : BEq α)
  证明: by
  have ⟨beq1⟩ := inst1
  congr
  funext x y
  exact h x y
-/
theorem beq_ext {α : Type*} (inst1 : BEq α) (inst2 : BEq α)
    (h : forall x y, @BEq.beq _ inst1 x y = @BEq.beq _ inst2 x y) :
    inst1 = inst2 := by
  have ⟨beq1⟩ := inst1
  congr
  funext x y
  exact h x y

set_option linter.overlappingInstances false in
/--
theorem `lawful_beq_subsingleton` / 定理 `lawful_beq_subsingleton`

English:
theorem lawful_beq_subsingleton
  statement: {α : Type*} (inst1 : BEq α) (inst2 : BEq α)
  proof: by
  ext
  simp

中文:
定理 lawful_beq_subsingleton
  结论: {α : 类型} (inst1 : BEq α) (inst2 : BEq α)
  证明: by
  ext
  simp
-/
theorem lawful_beq_subsingleton {α : Type*} (inst1 : BEq α) (inst2 : BEq α)
    [@LawfulBEq α inst1] [@LawfulBEq α inst2] :
    inst1 = inst2 := by
  ext
  simp
