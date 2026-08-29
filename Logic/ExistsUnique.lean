/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
module

public import Mathlib.Init

/-!
# `ExistsUnique`

This file defines the `ExistsUnique` predicate, notated as `∃!`, and proves some of its
basic properties.
-/

@[expose] public section

variable {α : Sort*}

/--
Definition of `ExistsUnique` / `ExistsUnique` 的定义

English:
definition ExistsUnique
  signature: (p : α -> Prop)
  body: exists x, p x ∧ forall y, p y -> y = x

中文:
定义 ExistsUnique
  签名: (p : α -> 命题)
  定义体: exists x, p x ∧ forall y, p y -> y = x
-/
def ExistsUnique (p : α -> Prop) := exists x, p x ∧ forall y, p y -> y = x

namespace Mathlib.Notation
open Lean

/-- Checks to see that `xs` has only one binder. -/
meta def isExplicitBinderSingular (xs : TSyntax ``explicitBinders) : Bool :=
  match xs with
  | `(explicitBinders| $_:binderIdent $[: $_]?) => true
  | `(explicitBinders| ($_:binderIdent : $_)) => true
  | _ => false

open TSyntax.Compat in
/--
`∃! x : α, p x` means that there exists a unique `x` in `α` such that `p x`.
This is notation for `ExistsUnique (fun (x : α) ↦ p x)`.

This notation does not allow multiple binders like `∃! (x : α) (y : β), p x y`
as a shorthand for `∃! (x : α), ∃! (y : β), p x y` since it is liable to be misunderstood.
Often, the intended meaning is instead `∃! q : α × β, p q.1 q.2`.
-/
macro "exists!" xs:explicitBinders ", " b:term : term => do
  if !isExplicitBinderSingular xs then
    Macro.throwErrorAt xs "\
      The `ExistsUnique` notation should not be used with more than one binder.\n\
      \n\
      The reason for this is that `exists! (x : α), exists! (y : β), p x y` has a completely different \
      meaning from `exists! q : α × β, p q.1 q.2`. \
      To prevent confusion, this notation requires that you be explicit \
      and use one with the correct interpretation."
  expandExplicitBinders ``ExistsUnique xs b

/--
Pretty-printing for `ExistsUnique`, following the same pattern as pretty printing for `Exists`.
However, it does *not* merge binders.
-/
@[app_unexpander ExistsUnique] meta def unexpandExistsUnique : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => $b) => `(exists! $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b) => `(exists! $x:ident : $t, $b)
  | _ => throw ()

/--
`∃! x ∈ s, p x` means `∃! x, x ∈ s ∧ p x`, which is to say that there exists a unique `x ∈ s`
such that `p x`.
Similarly, notations such as `∃! x ≤ n, p n` are supported,
using any relation defined using the `binder_predicate` command.
-/
syntax "exists! " binderIdent binderPred ", " term : term

macro_rules
  | `(exists! $x:ident $p:binderPred, $b) => `(exists! $x:ident, satisfies_binder_pred% $x $p ∧ $b)
  | `(exists! _ $p:binderPred, $b) => `(exists! x, satisfies_binder_pred% x $p ∧ $b)

end Mathlib.Notation

-- @[intro] -- TODO
/--
theorem `ExistsUnique.intro` / 定理 `ExistsUnique.intro`

English:
theorem ExistsUnique.intro
  statement: {p : α -> Prop} (w : α)
  proof: ⟨w, h₁, h₂⟩

中文:
定理 ExistsUnique.intro
  结论: {p : α -> 命题} (w : α)
  证明: ⟨w, h₁, h₂⟩
-/
theorem ExistsUnique.intro {p : α -> Prop} (w : α)
    (h₁ : p w) (h₂ : forall y, p y -> y = w) : exists! x, p x := ⟨w, h₁, h₂⟩

/--
theorem `ExistsUnique.elim` / 定理 `ExistsUnique.elim`

English:
theorem ExistsUnique.elim
  statement: {p : α -> Prop} {b : Prop}
  proof: Exists.elim h₂ (fun w hw => h₁ w (And.left hw) (And.right hw))

中文:
定理 ExistsUnique.elim
  结论: {p : α -> 命题} {b : 命题}
  证明: Exists.elim h₂ (fun w hw => h₁ w (And.left hw) (And.right hw))

Depends on / 依赖: And.left, And.right, Exists, Exists.elim
-/
theorem ExistsUnique.elim {p : α -> Prop} {b : Prop}
    (h₂ : exists! x, p x) (h₁ : forall x, p x -> (forall y, p y -> y = x) -> b) : b :=
  Exists.elim h₂ (fun w hw => h₁ w (And.left hw) (And.right hw))

/--
theorem `existsUnique_of_exists_of_unique` / 定理 `existsUnique_of_exists_of_unique`

English:
theorem existsUnique_of_exists_of_unique
  statement: {p : α -> Prop}
  proof: Exists.elim hex (fun x px => ExistsUnique.intro x px (fun y (h : p y) => hunique y x h px))

中文:
定理 existsUnique_of_exists_of_unique
  结论: {p : α -> 命题}
  证明: Exists.elim hex (fun x px => ExistsUnique.intro x px (fun y (h : p y) => hunique y x h px))

Depends on / 依赖: Exists, Exists.elim, ExistsUnique, ExistsUnique.intro, hunique
-/
theorem existsUnique_of_exists_of_unique {p : α -> Prop}
    (hex : exists x, p x) (hunique : forall y₁ y₂, p y₁ -> p y₂ -> y₁ = y₂) : exists! x, p x :=
  Exists.elim hex (fun x px => ExistsUnique.intro x px (fun y (h : p y) => hunique y x h px))

/--
theorem `ExistsUnique.exists` / 定理 `ExistsUnique.exists`

English:
theorem ExistsUnique.exists
  given: {p : α -> Prop}
  statement: (exists! x, p x) -> exists x, p x | ⟨x, h, _⟩ => ⟨x, h⟩

中文:
定理 ExistsUnique.exists
  条件: {p : α -> 命题}
  结论: (存在! x, p x) -> 存在 x, p x | ⟨x, h, _⟩ => ⟨x, h⟩
-/
theorem ExistsUnique.exists {p : α -> Prop} : (exists! x, p x) -> exists x, p x | ⟨x, h, _⟩ => ⟨x, h⟩

/--
theorem `ExistsUnique.unique` / 定理 `ExistsUnique.unique`

English:
theorem ExistsUnique.unique
  statement: {p : α -> Prop}
  proof: let ⟨_, _, hy⟩ := h; (hy _ py₁).trans (hy _ py₂).symm

中文:
定理 ExistsUnique.unique
  结论: {p : α -> 命题}
  证明: let ⟨_, _, hy⟩ := h; (hy _ py₁).trans (hy _ py₂).symm
-/
theorem ExistsUnique.unique {p : α -> Prop}
    (h : exists! x, p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂ :=
  let ⟨_, _, hy⟩ := h; (hy _ py₁).trans (hy _ py₂).symm

/--
theorem `ExistsUnique.choose_eq_iff` / 定理 `ExistsUnique.choose_eq_iff`

English:
theorem ExistsUnique.choose_eq_iff
  given: {p : α -> Prop} {a : α} (h : exists! x, p x)
  proof: ⟨fun ha => ha ▸ h.choose_spec.left, h.unique h.choose_spec.left⟩

中文:
定理 ExistsUnique.choose_eq_iff
  条件: {p : α -> 命题} {a : α} (h : 存在! x, p x)
  证明: ⟨fun ha => ha ▸ h.choose_spec.left, h.unique h.choose_spec.left⟩

Depends on / 依赖: choose_spec, h.choose_spec.left, h.unique, unique
-/
theorem ExistsUnique.choose_eq_iff {p : α -> Prop} {a : α} (h : exists! x, p x) :
    h.choose = a ↔ p a :=
  ⟨fun ha => ha ▸ h.choose_spec.left, h.unique h.choose_spec.left⟩

-- TODO
-- attribute [congr] forall_congr'
-- attribute [congr] exists_congr'

-- @[congr]
/--
theorem `existsUnique_congr` / 定理 `existsUnique_congr`

English:
theorem existsUnique_congr
  given: {p q : α -> Prop} (h : forall a, p a ↔ q a)
  statement: (exists! a, p a) ↔ exists! a, q a
  proof: exists_congr fun _ => and_congr (h _) forall_congr' fun _ => imp_congr_left (h _)

中文:
定理 existsUnique_congr
  条件: {p q : α -> 命题} (h : 对任意 a, p a ↔ q a)
  结论: (存在! a, p a) ↔ 存在! a, q a
  证明: exists_congr fun _ => and_congr (h _) forall_congr' fun _ => imp_congr_left (h _)

Depends on / 依赖: and_congr, exists_congr, forall_congr, imp_congr_left
-/
theorem existsUnique_congr {p q : α -> Prop} (h : forall a, p a ↔ q a) : (exists! a, p a) ↔ exists! a, q a :=
exists_congr fun _ => and_congr (h _) forall_congr' fun _ => imp_congr_left (h _)

/--
theorem `existsUnique_iff_exists` / 定理 `existsUnique_iff_exists`

English:
theorem existsUnique_iff_exists
  given: [Subsingleton α] {p : α -> Prop}
  proof: ⟨fun h => h.exists, Exists.imp fun x hx => ⟨hx, fun y _ => Subsingleton.elim y x⟩⟩

中文:
定理 existsUnique_iff_exists
  条件: [Subsingleton α] {p : α -> 命题}
  证明: ⟨fun h => h.exists, Exists.imp fun x hx => ⟨hx, fun y _ => Subsingleton.elim y x⟩⟩
-/
@[simp] theorem existsUnique_iff_exists [Subsingleton α] {p : α -> Prop} :
    (exists! x, p x) ↔ exists x, p x :=
  ⟨fun h => h.exists, Exists.imp fun x hx => ⟨hx, fun y _ => Subsingleton.elim y x⟩⟩

/--
theorem `existsUnique_const` / 定理 `existsUnique_const`

English:
theorem existsUnique_const
  given: {b : Prop} (α : Sort*) [i : Nonempty α] [Subsingleton α]
  proof: by simp

中文:
定理 existsUnique_const
  条件: {b : 命题} (α : Sort*) [i : Nonempty α] [Subsingleton α]
  证明: by simp
-/
theorem existsUnique_const {b : Prop} (α : Sort*) [i : Nonempty α] [Subsingleton α] :
    (exists! _ : α, b) ↔ b := by simp

/--
theorem `existsUnique_eq` / 定理 `existsUnique_eq`

English:
theorem existsUnique_eq
  given: {a' : α}
  statement: exists! a, a = a'
  proof: by
  simp only [eq_comm, ExistsUnique, and_self, forall_eq', exists_eq']

中文:
定理 existsUnique_eq
  条件: {a' : α}
  结论: 存在! a, a = a'
  证明: by
  simp only [eq_comm, ExistsUnique, and_self, forall_eq', exists_eq']
-/
@[simp] theorem existsUnique_eq {a' : α} : exists! a, a = a' := by
  simp only [eq_comm, ExistsUnique, and_self, forall_eq', exists_eq']

/--
theorem `existsUnique_eq'` / 定理 `existsUnique_eq'`

English:
theorem existsUnique_eq'
  given: {a' : α}
  statement: exists! a, a' = a
  proof: by
  simp only [ExistsUnique, and_self, forall_eq', exists_eq']

中文:
定理 existsUnique_eq'
  条件: {a' : α}
  结论: 存在! a, a' = a
  证明: by
  simp only [ExistsUnique, and_self, forall_eq', exists_eq']
-/
@[simp] theorem existsUnique_eq' {a' : α} : exists! a, a' = a := by
  simp only [ExistsUnique, and_self, forall_eq', exists_eq']

/--
theorem `existsUnique_prop` / 定理 `existsUnique_prop`

English:
theorem existsUnique_prop
  given: {p q : Prop}
  statement: (exists! _ : p, q) ↔ p ∧ q
  proof: by simp

中文:
定理 existsUnique_prop
  条件: {p q : 命题}
  结论: (存在! _ : p, q) ↔ p ∧ q
  证明: by simp
-/
theorem existsUnique_prop {p q : Prop} : (exists! _ : p, q) ↔ p ∧ q := by simp

/--
theorem `existsUnique_false` / 定理 `existsUnique_false`

English:
theorem existsUnique_false
  statement: ¬exists! _ : α, False
  proof: fun ⟨_, h, _⟩ => h

中文:
定理 existsUnique_false
  结论: ¬存在! _ : α, False
  证明: fun ⟨_, h, _⟩ => h
-/
@[simp] theorem existsUnique_false : ¬exists! _ : α, False := fun ⟨_, h, _⟩ => h

/--
theorem `existsUnique_prop_of_true` / 定理 `existsUnique_prop_of_true`

English:
theorem existsUnique_prop_of_true
  given: {p : Prop} {q : p -> Prop} (h : p)
  statement: (exists! h' : p, q h') ↔ q h
  proof: @existsUnique_const (q h) p ⟨h⟩ _

中文:
定理 existsUnique_prop_of_true
  条件: {p : 命题} {q : p -> 命题} (h : p)
  结论: (存在! h' : p, q h') ↔ q h
  证明: @existsUnique_const (q h) p ⟨h⟩ _

Depends on / 依赖: existsUnique_const
-/
theorem existsUnique_prop_of_true {p : Prop} {q : p -> Prop} (h : p) : (exists! h' : p, q h') ↔ q h :=
  @existsUnique_const (q h) p ⟨h⟩ _

/--
theorem `ExistsUnique.elim₂` / 定理 `ExistsUnique.elim₂`

English:
theorem ExistsUnique.elim₂
  statement: {p : α -> Sort*} [forall x, Subsingleton (p x)]
  proof: by
  simp only [existsUnique_iff_exists] at h₂
  apply h₂.elim
  exact fun x ⟨hxp, hxq⟩ H => h₁ x hxp hxq fun y hyp hyq => H y ⟨hyp, hyq⟩

中文:
定理 ExistsUnique.elim₂
  结论: {p : α -> Sort*} [对任意 x, Subsingleton (p x)]
  证明: by
  simp only [existsUnique_iff_exists] at h₂
  apply h₂.elim
  exact fun x ⟨hxp, hxq⟩ H => h₁ x hxp hxq fun y hyp hyq => H y ⟨hyp, hyq⟩

Depends on / 依赖: existsUnique_iff_exists
-/
theorem ExistsUnique.elim₂ {p : α -> Sort*} [forall x, Subsingleton (p x)]
    {q : forall (x) (_ : p x), Prop} {b : Prop} (h₂ : exists! x, exists! h : p x, q x h)
    (h₁ : forall (x) (h : p x), q x h -> (forall (y) (hy : p y), q y hy -> y = x) -> b) : b := by
  simp only [existsUnique_iff_exists] at h₂
  apply h₂.elim
  exact fun x ⟨hxp, hxq⟩ H => h₁ x hxp hxq fun y hyp hyq => H y ⟨hyp, hyq⟩

/--
theorem `ExistsUnique.intro₂` / 定理 `ExistsUnique.intro₂`

English:
theorem ExistsUnique.intro₂
  statement: {p : α -> Sort*} [forall x, Subsingleton (p x)]
  proof: by
  simp only [existsUnique_iff_exists]
  exact ExistsUnique.intro w ⟨hp, hq⟩ fun y ⟨hyp, hyq⟩ => H y hyp hyq

中文:
定理 ExistsUnique.intro₂
  结论: {p : α -> Sort*} [对任意 x, Subsingleton (p x)]
  证明: by
  simp only [existsUnique_iff_exists]
  exact ExistsUnique.intro w ⟨hp, hq⟩ fun y ⟨hyp, hyq⟩ => H y hyp hyq

Depends on / 依赖: ExistsUnique, ExistsUnique.intro, existsUnique_iff_exists
-/
theorem ExistsUnique.intro₂ {p : α -> Sort*} [forall x, Subsingleton (p x)]
    {q : forall (x : α) (_ : p x), Prop} (w : α) (hp : p w) (hq : q w hp)
    (H : forall (y) (hy : p y), q y hy -> y = w) : exists! x, exists! hx : p x, q x hx := by
  simp only [existsUnique_iff_exists]
  exact ExistsUnique.intro w ⟨hp, hq⟩ fun y ⟨hyp, hyq⟩ => H y hyp hyq

/--
theorem `ExistsUnique.exists₂` / 定理 `ExistsUnique.exists₂`

English:
theorem ExistsUnique.exists₂
  statement: {p : α -> Sort*} {q : forall (x : α) (_ : p x), Prop}
  proof: h.exists.imp fun _ hx => hx.exists

中文:
定理 ExistsUnique.exists₂
  结论: {p : α -> Sort*} {q : 对任意 (x : α) (_ : p x), 命题}
  证明: h.exists.imp fun _ hx => hx.exists

Depends on / 依赖: h.exists.imp, hx.exists
-/
theorem ExistsUnique.exists₂ {p : α -> Sort*} {q : forall (x : α) (_ : p x), Prop}
    (h : exists! x, exists! hx : p x, q x hx) : exists (x : _) (hx : p x), q x hx :=
  h.exists.imp fun _ hx => hx.exists

/--
theorem `ExistsUnique.unique₂` / 定理 `ExistsUnique.unique₂`

English:
theorem ExistsUnique.unique₂
  statement: {p : α -> Sort*} [forall x, Subsingleton (p x)]
  proof: by
  simp only [existsUnique_iff_exists] at h
  exact h.unique ⟨hpy₁, hqy₁⟩ ⟨hpy₂, hqy₂⟩

中文:
定理 ExistsUnique.unique₂
  结论: {p : α -> Sort*} [对任意 x, Subsingleton (p x)]
  证明: by
  simp only [existsUnique_iff_exists] at h
  exact h.unique ⟨hpy₁, hqy₁⟩ ⟨hpy₂, hqy₂⟩

Depends on / 依赖: existsUnique_iff_exists, h.unique, unique
-/
theorem ExistsUnique.unique₂ {p : α -> Sort*} [forall x, Subsingleton (p x)]
    {q : forall (x : α) (_ : p x), Prop} (h : exists! x, exists! hx : p x, q x hx) {y₁ y₂ : α}
    (hpy₁ : p y₁) (hqy₁ : q y₁ hpy₁) (hpy₂ : p y₂) (hqy₂ : q y₂ hpy₂) : y₁ = y₂ := by
  simp only [existsUnique_iff_exists] at h
  exact h.unique ⟨hpy₁, hqy₁⟩ ⟨hpy₂, hqy₂⟩

/--
Instance `List.decidableBExistsUnique` / 实例 `List.decidableBExistsUnique`

English:
instance List.decidableBExistsUnique
  signature: {α : Type*} [DecidableEq α] (p : α -> Prop) [DecidablePred p]
  body: List.decidableBExistsUnique p xs
      decidable_of_iff (exists! x, x in xs ∧ p x) (by grind)

中文:
实例 List.decidableBExistsUnique
  签名: {α : 类型} [DecidableEq α] (p : α -> 命题) [DecidablePred p]
  定义体: List.decidableBExistsUnique p xs
      decidable_of_iff (exists! x, x in xs ∧ p x) (by grind)

Depends on / 依赖: List.decidableBExistsUnique, decidableBExistsUnique
-/
instance List.decidableBExistsUnique {α : Type*} [DecidableEq α] (p : α -> Prop) [DecidablePred p] :
    (l : List α) -> Decidable (exists! x, x in l ∧ p x)
| [] => .isFalse by simp
  | x :: xs =>
    if hx : p x then
      decidable_of_iff (forall y in xs, p y -> x = y) (⟨fun h => ⟨x, by grind⟩,
        fun ⟨z, h⟩ y hy hp => (h.2 x ⟨mem_cons_self, hx⟩).trans (by grind)⟩)
    else
      have := List.decidableBExistsUnique p xs
      decidable_of_iff (exists! x, x in xs ∧ p x) (by grind)
