/-
Copyright (c) 2024 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
module

public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Order.Basic

/-!
# Interaction between `Sum.elim`, `≤`, and `0` or `1`

This file provides basic API for part-wise comparison of `Sum.elim` vectors against `0` or `1`.
-/

public section

namespace Sum

variable {α₁ α₂ β : Type*} [LE β] [One β] {v₁ : α₁ -> β} {v₂ : α₂ -> β}

@[to_additive]
/--
lemma `one_le_elim_iff` / 引理 `one_le_elim_iff`

English:
lemma one_le_elim_iff
  statement: 1 <= Sum.elim v₁ v₂ ↔ 1 <= v₁ ∧ 1 <= v₂
  proof: const_le_elim_iff

@[to_additive]

中文:
引理 one_le_elim_iff
  结论: 1 <= 和.elim v₁ v₂ ↔ 1 <= v₁ ∧ 1 <= v₂
  证明: const_le_elim_iff

@[to_additive]

Depends on / 依赖: const_le_elim_iff
-/
lemma one_le_elim_iff : 1 <= Sum.elim v₁ v₂ ↔ 1 <= v₁ ∧ 1 <= v₂ :=
  const_le_elim_iff

@[to_additive]
/--
lemma `elim_le_one_iff` / 引理 `elim_le_one_iff`

English:
lemma elim_le_one_iff
  statement: Sum.elim v₁ v₂ <= 1 ↔ v₁ <= 1 ∧ v₂ <= 1
  proof: elim_le_const_iff

中文:
引理 elim_le_one_iff
  结论: 和.elim v₁ v₂ <= 1 ↔ v₁ <= 1 ∧ v₂ <= 1
  证明: elim_le_const_iff

Depends on / 依赖: elim_le_const_iff
-/
lemma elim_le_one_iff : Sum.elim v₁ v₂ <= 1 ↔ v₁ <= 1 ∧ v₂ <= 1 :=
  elim_le_const_iff

end Sum
