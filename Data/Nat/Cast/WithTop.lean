/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop

/-!
# Lemma about the coercion `ℕ → WithBot ℕ`.

An orphaned lemma about casting from `ℕ` to `WithBot ℕ`,
exiled here during the port to minimize imports of `Algebra.Order.Ring.Rat`.
-/

public section

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: WellFoundedRelation (WithTop Nat)
  body: (· < ·)
  wf := IsWellFounded.wf

中文:
实例 :
  签名: 良基关系 (WithTop 自然数)
  定义体: (· < ·)
  wf := IsWellFounded.wf
-/
instance : WellFoundedRelation (WithTop Nat) where
  rel := (· < ·)
  wf := IsWellFounded.wf

/--
theorem `Nat.cast_withTop` / 定理 `Nat.cast_withTop`

English:
theorem Nat.cast_withTop
  given: (n : Nat)
  statement: Nat.cast n = WithTop.some n
  proof: rfl

中文:
定理 自然数.cast_withTop
  条件: (n : 自然数)
  结论: 自然数.cast n = WithTop.some n
  证明: rfl
-/
theorem Nat.cast_withTop (n : Nat) : Nat.cast n = WithTop.some n :=
  rfl

/--
theorem `Nat.cast_withBot` / 定理 `Nat.cast_withBot`

English:
theorem Nat.cast_withBot
  given: (n : Nat)
  statement: Nat.cast n = WithBot.some n
  proof: rfl

中文:
定理 自然数.cast_withBot
  条件: (n : 自然数)
  结论: 自然数.cast n = WithBot.some n
  证明: rfl
-/
theorem Nat.cast_withBot (n : Nat) : Nat.cast n = WithBot.some n :=
  rfl
