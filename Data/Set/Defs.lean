/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

public import Batteries.Tactic.Alias
public import Batteries.Util.ExtendedBinder
public import Mathlib.Tactic.SetNotationForOrder

import Mathlib.Tactic.ToDual

/-!
# Sets

This file sets up the theory of sets whose elements have a given type.

## Main definitions

Given a type `X` and a predicate `p : X → Prop`:

* `Set X` : the type of sets whose elements have type `X`
* `{a : X | p a} : Set X` : the set of all elements of `X` satisfying `p`
* `{a | p a} : Set X` : a more concise notation for `{a : X | p a}`
* `{f x y | (x : X) (y : Y)} : Set Z` : a more concise notation for `{z : Z | ∃ x y, f x y = z}`
* `{a ∈ S | p a} : Set X` : given `S : Set X`, the subset of `S` consisting of
  its elements satisfying `p`.

## Implementation issues

As in Lean 3, `Set X := X → Prop`
This file is a port of the core Lean 3 file `lib/lean/library/init/data/set.lean`.

-/

@[expose] public section

open Lean Elab Term Meta Batteries.ExtendedBinder

universe u
variable {α : Type u}

/-- A set is a collection of elements of some type `α`.

Although `Set` is defined as `α → Prop`, this is an implementation detail which should not be
relied on. Instead, `Set.ofPred` (also written `{x | p x}`) and membership of a set (`∈`) should be
used to convert between sets and predicates.
-/
@[use_set_notation_for_order]
/--
Definition of `Set` / `Set` 的定义

English:
definition Set
  signature: (α : Type u)
  body: α -> Prop

中文:
定义 Set
  签名: (α : 类型u)
  定义体: α -> Prop
-/
def Set (α : Type u) := α -> Prop

/-
We don't translate the order on sets (i.e. turning `s ⊆ t` into `t ⊆ s`).
This is because for example the following theorems should be dual
```
theorem sSup_le_sSup {s t : Set α} (h : s ⊆ t) : sSup s ≤ sSup t
theorem sInf_le_sInf {s t : Set α} (h : s ⊆ t) : sInf t ≤ sInf s
```
Additionally, dualizing the order on sets would mean that a set is dual to its complement.
But we would like to dualize set intervals such that e.g. `Ico a b` is dual to `Ioc b a`.
-/
attribute [to_dual_dont_translate] Set

/-- Turn a predicate `p : α → Prop` into a set, also written as `{x | p x}` -/
@[implicit_reducible]
/--
Definition of `Set.ofPred` / `Set.ofPred` 的定义

English:
definition Set.ofPred
  signature: {α : Type u} (p : α -> Prop)
  body: p

@[deprecated (since := "2026-07-09")] alias setOf := Set.ofPred

中文:
定义 Set.ofPred
  签名: {α : 类型u} (p : α -> 命题)
  定义体: p

@[deprecated (since := "2026-07-09")] alias setOf := Set.ofPred
-/
def Set.ofPred {α : Type u} (p : α -> Prop) : Set α :=
  p

@[deprecated (since := "2026-07-09")] alias setOf := Set.ofPred

namespace Set

/-- Membership in a set -/
@[implicit_reducible]
/--
Definition of `Mem` / `Mem` 的定义

English:
definition Mem
  signature: (s : Set α) (a : α)
  body: s a

中文:
定义 Mem
  签名: (s : Set α) (a : α)
  定义体: s a
-/
protected def Mem (s : Set α) (a : α) : Prop :=
  s a

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership α (Set α)
  body: ⟨Set.Mem⟩

@[ext, grind ext]

中文:
实例 :
  签名: Membership α (Set α)
  定义体: ⟨Set.Mem⟩

@[ext, grind ext]

Depends on / 依赖: Set.Mem
-/
instance : Membership α (Set α) :=
  ⟨Set.Mem⟩

@[ext, grind ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {a b : Set α} (h : forall (x : α), x in a ↔ x in b)
  statement: a = b
  proof: funext (fun x => propext (h x))

中文:
定理 ext
  条件: {a b : Set α} (h : 对任意 (x : α), x in a ↔ x in b)
  结论: a = b
  证明: funext (fun x => propext (h x))

Depends on / 依赖: infer_instance, propext
-/
theorem ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b :=
  funext (fun x => propext (h x))

/--
Definition of `Subset` / `Subset` 的定义

English:
definition Subset
  signature: (s₁ s₂ : Set α)
  body: forall ⦃a⦄, a in s₁ -> a in s₂

中文:
定义 Subset
  签名: (s₁ s₂ : Set α)
  定义体: forall ⦃a⦄, a in s₁ -> a in s₂
-/
protected def Subset (s₁ s₂ : Set α) :=
  forall ⦃a⦄, a in s₁ -> a in s₂

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE (Set α)
  body: ⟨Set.Subset⟩

中文:
实例 :
  签名: LE (Set α)
  定义体: ⟨Set.Subset⟩

Depends on / 依赖: Set.Subset, Subset
-/
instance : LE (Set α) :=
  ⟨Set.Subset⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EmptyCollection (Set α)
  body: ⟨fun _ => False⟩

中文:
实例 :
  签名: EmptyCollection (Set α)
  定义体: ⟨fun _ => False⟩
-/
instance : EmptyCollection (Set α) :=
  ⟨fun _ => False⟩

end Set

namespace Mathlib.Meta

/-- Set builder syntax. This can be elaborated to either a `Set` or a `Finset` depending on context.

The elaborators for this syntax are located in:
* `Data.Set.Defs` for the `Set` builder notation elaborator for syntax of the form `{x | p x}`,
  `{x : α | p x}`, `{binder x | p x}`.
* `Data.Finset.Basic` for the `Finset` builder notation elaborator for syntax of the form
  `{x ∈ s | p x}`.
* `Data.Fintype.Basic` for the `Finset` builder notation elaborator for syntax of the form
  `{x | p x}`, `{x : α | p x}`, `{x ∉ s | p x}`, `{x ≠ a | p x}`.
* `Order.LocallyFinite.Basic` for the `Finset` builder notation elaborator for syntax of the form
  `{x ≤ a | p x}`, `{x ≥ a | p x}`, `{x < a | p x}`, `{x > a | p x}`.
-/
syntax (name := setBuilder) "{" extBinder " | " term "}" : term

/-- Elaborate set builder notation for `Set`.

* `{x | p x}` is elaborated as `Set.ofPred fun x ↦ p x`
* `{x : α | p x}` is elaborated as `Set.ofPred fun x : α ↦ p x`
* `{binder x | p x}`, where `x` is bound by the `binder` binder, is elaborated as
  `{x | binder x ∧ p x}`. The typical example is `{x ∈ s | p x}`, which is elaborated as
  `{x | x ∈ s ∧ p x}`. The possible binders are
  * `· ∈ s`, `· ∉ s`
  * `· ⊆ s`, `· ⊂ s`, `· ⊇ s`, `· ⊃ s`
  * `· ≤ a`, `· ≥ a`, `· < a`, `· > a`, `· ≠ a`

  More binders can be declared using the `binder_predicate` command, see `Init.BinderPredicates` for
  more info.

See also
* `Data.Finset.Basic` for the `Finset` builder notation elaborator partly overriding this one for
  syntax of the form `{x ∈ s | p x}`.
* `Data.Fintype.Basic` for the `Finset` builder notation elaborator partly overriding this one for
  syntax of the form `{x | p x}`, `{x : α | p x}`, `{x ∉ s | p x}`, `{x ≠ a | p x}`.
* `Order.LocallyFinite.Basic` for the `Finset` builder notation elaborator partly overriding this
  one for syntax of the form `{x ≤ a | p x}`, `{x ≥ a | p x}`, `{x < a | p x}`, `{x > a | p x}`.
-/
@[term_elab setBuilder]
meta def elabSetBuilder : TermElab
  | `({ $x:ident | $p }), expectedType? => do
    elabTerm (← `(Set.ofPred fun $x:ident => $p)) expectedType?
  | `({ $x:ident : $t | $p }), expectedType? => do
    elabTerm (← `(Set.ofPred fun $x:ident : $t => $p)) expectedType?
  | `({ $x:ident $b:binderPred | $p }), expectedType? => do
    elabTerm (← `(Set.ofPred fun $x:ident => satisfies_binder_pred% $x $b ∧ $p)) expectedType?
  | _, _ => throwUnsupportedSyntax

/-- Unexpander for set builder notation. -/
@[app_unexpander Set.ofPred]
meta def ofPred.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ fun $x:ident => $p) => `({ $x:ident | $p })
  | `($_ fun ($x:ident : $ty:term) => $p) => `({ $x:ident : $ty:term | $p })
  | _ => throw ()

open Batteries.ExtendedBinder in
/--
`{ f x y | (x : X) (y : Y) }` is notation for the set of elements `f x y` constructed from the
binders `x` and `y`, equivalent to `{z : Z | ∃ x y, f x y = z}`.

If `f x y` is a single identifier, it must be parenthesized to avoid ambiguity with `{x | p x}`;
for instance, `{(x) | (x : Nat) (y : Nat) (_hxy : x = y^2)}`.
-/
macro (priority := low) "{" t:term " | " bs:extBinders "}" : term =>
  `({x | existsᵉ $bs:extBinders, $t = x})

/--
* `{ pat : X | p }` is notation for pattern matching in set-builder notation,
  where `pat` is a pattern that is matched by all objects of type `X`
  and `p` is a proposition that can refer to variables in the pattern.
  It is the set of all objects of type `X` which, when matched with the pattern `pat`,
  make `p` come out true.
* `{ pat | p }` is the same, but in the case when the type `X` can be inferred.

For example, `{ (m, n) : ℕ × ℕ | m * n = 12 }` denotes the set of all ordered pairs of
natural numbers whose product is 12.

Note that if the type ascription is left out and `p` can be interpreted as an extended binder,
then the extended binder interpretation will be used. For example, `{ n + 1 | n < 3 }` will
be interpreted as `{ x : Nat | ∃ n < 3, n + 1 = x }` rather than using pattern matching.
-/
macro (name := macroPattSetBuilder) (priority := low - 1)
  "{" pat:term " : " t:term " | " p:term "}" : term =>
  `({ x : $t | match x with | $pat => $p })

@[inherit_doc macroPattSetBuilder]
macro (priority := low - 1) "{" pat:term " | " p:term "}" : term =>
  `({ x | match x with | $pat => $p })

/-- Pretty printing for set-builder notation with pattern matching. -/
@[app_unexpander Set.ofPred]
meta def ofPredPatternMatchUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ fun $x:ident => match $y:ident with | $pat => $p) =>
      if x == y then
        `({ $pat:term | $p:term })
      else
        throw ()
  | `($_ fun ($x:ident : $ty:term) => match $y:ident with | $pat => $p) =>
      if x == y then
        `({ $pat:term : $ty:term | $p:term })
      else
        throw ()
  | _ => throw ()

end Mathlib.Meta

namespace Set

/--
Definition of `univ` / `univ` 的定义

English:
definition univ
  signature: : Set α
  body: {_a | True}

中文:
定义 univ
  签名: : Set α
  定义体: {_a | True}
-/
def univ : Set α := {_a | True}

/--
Definition of `insert` / `insert` 的定义

English:
definition insert
  signature: (a : α) (s : Set α)
  body: {b | b = a ∨ b in s}

中文:
定义 insert
  签名: (a : α) (s : Set α)
  定义体: {b | b = a ∨ b in s}
-/
protected def insert (a : α) (s : Set α) : Set α := {b | b = a ∨ b in s}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Insert α (Set α)
  body: ⟨Set.insert⟩

中文:
实例 :
  签名: Insert α (Set α)
  定义体: ⟨Set.insert⟩

Depends on / 依赖: Set.insert, insert
-/
instance : Insert α (Set α) := ⟨Set.insert⟩

/--
Definition of `singleton` / `singleton` 的定义

English:
definition singleton
  signature: (a : α)
  body: {b | b = a}

中文:
定义 singleton
  签名: (a : α)
  定义体: {b | b = a}
-/
protected def singleton (a : α) : Set α := {b | b = a}

/--
Instance `instSingletonSet` / 实例 `instSingletonSet`

English:
instance instSingletonSet
  signature: : Singleton α (Set α)
  body: ⟨Set.singleton⟩

中文:
实例 instSingletonSet
  签名: : Singleton α (Set α)
  定义体: ⟨Set.singleton⟩

Depends on / 依赖: Set.singleton, singleton
-/
instance instSingletonSet : Singleton α (Set α) := ⟨Set.singleton⟩

/--
Definition of `union` / `union` 的定义

English:
definition union
  signature: (s₁ s₂ : Set α)
  body: {a | a in s₁ ∨ a in s₂}

中文:
定义 union
  签名: (s₁ s₂ : Set α)
  定义体: {a | a in s₁ ∨ a in s₂}
-/
protected def union (s₁ s₂ : Set α) : Set α := {a | a in s₁ ∨ a in s₂}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Union (Set α)
  body: ⟨Set.union⟩

中文:
实例 :
  签名: Union (Set α)
  定义体: ⟨Set.union⟩

Depends on / 依赖: Set.union
-/
instance : Union (Set α) := ⟨Set.union⟩

/--
Definition of `inter` / `inter` 的定义

English:
definition inter
  signature: (s₁ s₂ : Set α)
  body: {a | a in s₁ ∧ a in s₂}

中文:
定义 inter
  签名: (s₁ s₂ : Set α)
  定义体: {a | a in s₁ ∧ a in s₂}
-/
protected def inter (s₁ s₂ : Set α) : Set α := {a | a in s₁ ∧ a in s₂}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inter (Set α)
  body: ⟨Set.inter⟩

中文:
实例 :
  签名: 整数er (Set α)
  定义体: ⟨Set.inter⟩

Depends on / 依赖: Set.inter
-/
instance : Inter (Set α) := ⟨Set.inter⟩

/--
Definition of `compl` / `compl` 的定义

English:
definition compl
  signature: (s : Set α)
  body: {a | a ∉ s}

中文:
定义 compl
  签名: (s : Set α)
  定义体: {a | a ∉ s}
-/
protected def compl (s : Set α) : Set α := {a | a ∉ s}

/--
Definition of `diff` / `diff` 的定义

English:
definition diff
  signature: (s t : Set α)
  body: {a in s | a ∉ t}

中文:
定义 diff
  签名: (s t : Set α)
  定义体: {a in s | a ∉ t}
-/
protected def diff (s t : Set α) : Set α := {a in s | a ∉ t}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SDiff (Set α)
  body: ⟨Set.diff⟩

中文:
实例 :
  签名: SDiff (Set α)
  定义体: ⟨Set.diff⟩

Depends on / 依赖: Set.diff
-/
instance : SDiff (Set α) := ⟨Set.diff⟩

/--
Definition of `powerset` / `powerset` 的定义

English:
definition powerset
  signature: (s : Set α)
  body: {t | t subseteq s}

@[inherit_doc] prefix:100 "𝒫 " => powerset

universe v in

中文:
定义 powerset
  签名: (s : Set α)
  定义体: {t | t subseteq s}

@[inherit_doc] prefix:100 "𝒫 " => powerset

universe v in

Depends on / 依赖: subseteq
-/
def powerset (s : Set α) : Set (Set α) := {t | t subseteq s}

@[inherit_doc] prefix:100 "𝒫 " => powerset

universe v in
/--
Definition of `image` / `image` 的定义

English:
definition image
  signature: {β : Type v} (f : α -> β) (s : Set α)
  body: {f a | a in s}

中文:
定义 image
  签名: {β : 类型v} (f : α -> β) (s : Set α)
  定义体: {f a | a in s}
-/
def image {β : Type v} (f : α -> β) (s : Set α) : Set β := {f a | a in s}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Functor Set
  body: @Set.image

中文:
实例 :
  签名: Functor Set
  定义体: @Set.image

Depends on / 依赖: Set.image
-/
instance : Functor Set where map := @Set.image

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulFunctor Set
  body: funext fun _ => propext ⟨fun ⟨_, sb, rfl⟩ => sb, fun sb => ⟨_, sb, rfl⟩⟩
comp_map g h _ := funext fun c => propext
    ⟨fun ⟨a, ⟨h₁, h₂⟩⟩ => ⟨g a, ⟨⟨a, ⟨h₁, rfl⟩⟩, h₂⟩⟩,
     fun ⟨_, ⟨⟨a, ⟨h₁, h₂⟩⟩, h₃⟩⟩ => ⟨a, ⟨h₁, show h (g a) = c from h₂ ▸ h₃⟩⟩⟩
  map_const := rfl

中文:
实例 :
  签名: LawfulFunctor Set
  定义体: funext fun _ => propext ⟨fun ⟨_, sb, rfl⟩ => sb, fun sb => ⟨_, sb, rfl⟩⟩
comp_map g h _ := funext fun c => propext
    ⟨fun ⟨a, ⟨h₁, h₂⟩⟩ => ⟨g a, ⟨⟨a, ⟨h₁, rfl⟩⟩, h₂⟩⟩,
     fun ⟨_, ⟨⟨a, ⟨h₁, h₂⟩⟩, h₃⟩⟩ => ⟨a, ⟨h₁, show h (g a) = c from h₂ ▸ h₃⟩⟩⟩
  map_const := rfl

Depends on / 依赖: propext
-/
instance : LawfulFunctor Set where
  id_map _ := funext fun _ => propext ⟨fun ⟨_, sb, rfl⟩ => sb, fun sb => ⟨_, sb, rfl⟩⟩
comp_map g h _ := funext fun c => propext
    ⟨fun ⟨a, ⟨h₁, h₂⟩⟩ => ⟨g a, ⟨⟨a, ⟨h₁, rfl⟩⟩, h₂⟩⟩,
     fun ⟨_, ⟨⟨a, ⟨h₁, h₂⟩⟩, h₃⟩⟩ => ⟨a, ⟨h₁, show h (g a) = c from h₂ ▸ h₃⟩⟩⟩
  map_const := rfl

/--
Definition of `Nonempty` / `Nonempty` 的定义

English:
definition Nonempty
  signature: (s : Set α)
  body: exists x, x in s

中文:
定义 Nonempty
  签名: (s : Set α)
  定义体: exists x, x in s
-/
protected def Nonempty (s : Set α) : Prop :=
  exists x, x in s

end Set
