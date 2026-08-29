/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Sub.Basic

/-!
# `Nat.Upto`

`Nat.Upto p`, with `p` a predicate on `ℕ`, is a subtype of elements `n : ℕ` such that no value
(strictly) below `n` satisfies `p`.

This type has the property that `>` is well-founded when `∃ i, p i`, which allows us to implement
searches on `ℕ`, starting at `0` and with an unknown upper-bound.

It is similar to the well-founded relation constructed to define `Nat.find` with
the difference that, in `Nat.Upto p`, `p` does not need to be decidable. In fact,
`Nat.find` could be slightly altered to factor decidability out of its
well-founded relation and would then fulfill the same purpose as this file.
-/

@[expose] public section


namespace Nat

/--
Definition of `Upto` / `Upto` 的定义

English:
abbreviation Upto
  signature: (p : Nat -> Prop)
  body: { i : Nat // forall j < i, ¬p j }

中文:
缩写 Upto
  签名: (p : 自然数 -> 命题)
  定义体: { i : Nat // forall j < i, ¬p j }
-/
abbrev Upto (p : Nat -> Prop) : Type :=
  { i : Nat // forall j < i, ¬p j }

namespace Upto

variable {p : Nat -> Prop}

/--
Definition of `GT` / `GT` 的定义

English:
definition GT
  signature: (p) (x y : Upto p)
  body: x.1 > y.1

中文:
定义 GT
  签名: (p) (x y : Upto p)
  定义体: x.1 > y.1
-/
protected def GT (p) (x y : Upto p) : Prop :=
  x.1 > y.1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LT (Upto p)
  body: ⟨fun x y => x.1 < y.1⟩

中文:
实例 :
  签名: LT (Upto p)
  定义体: ⟨fun x y => x.1 < y.1⟩
-/
instance : LT (Upto p) :=
  ⟨fun x y => x.1 < y.1⟩

/--
theorem `wf` / 定理 `wf`

English:
theorem wf
  statement: (exists x, p x) -> WellFounded (Upto.GT p)

中文:
定理 wf
  结论: (存在 x, p x) -> WellFounded (Upto.GT p)
-/
protected theorem wf : (exists x, p x) -> WellFounded (Upto.GT p)
  | ⟨x, h⟩ => by
    suffices Upto.GT p = InvImage (· < ·) fun y : Nat.Upto p => x - y.val by
      rw [this]
      exact (measure _).wf
    ext ⟨a, ha⟩ ⟨b, _⟩
    dsimp [InvImage, Upto.GT]
    rw [tsub_lt_tsub_iff_left_of_le (le_of_not_gt fun h' => ha _ h' h)]

/--
Definition of `zero` / `zero` 的定义

English:
definition zero
  signature: : Nat.Upto p
  body: ⟨0, fun _ h => False.elim (Nat.not_lt_zero _ h)⟩

中文:
定义 zero
  签名: : 自然数.Upto p
  定义体: ⟨0, fun _ h => False.elim (Nat.not_lt_zero _ h)⟩

Depends on / 依赖: False.elim, Nat.not_lt_zero, not_lt_zero
-/
def zero : Nat.Upto p :=
  ⟨0, fun _ h => False.elim (Nat.not_lt_zero _ h)⟩

/--
Definition of `succ` / `succ` 的定义

English:
definition succ
  signature: (x : Nat.Upto p) (h : ¬p x.val)
  body: ⟨x.val.succ, fun j h' => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 h' with (h' | rfl) <;> [exact x.2 _ h'; exact h]⟩

中文:
定义 succ
  签名: (x : 自然数.Upto p) (h : ¬p x.val)
  定义体: ⟨x.val.succ, fun j h' => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 h' with (h' | rfl) <;> [exact x.2 _ h'; exact h]⟩

Depends on / 依赖: Nat.lt_succ_iff_lt_or_eq, lt_succ_iff_lt_or_eq, x.val.succ
-/
def succ (x : Nat.Upto p) (h : ¬p x.val) : Nat.Upto p :=
  ⟨x.val.succ, fun j h' => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 h' with (h' | rfl) <;> [exact x.2 _ h'; exact h]⟩

end Upto

end Nat
