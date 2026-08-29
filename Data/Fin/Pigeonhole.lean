/-
Copyright (c) 2025 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
module

public import Mathlib.Data.Fintype.Card

/-!
# Pigeonhole-like results for Fin

This adapts Pigeonhole-like results from `Mathlib.Data.Fintype.Card` to the setting where the map
has the type `f : Fin m → Fin n`.
-/

public section

namespace Fin

variable {m n : Nat}

/--
theorem `le_of_injective` / 定理 `le_of_injective`

English:
theorem le_of_injective
  given: (f : Fin m -> Fin n) (hf : f.Injective)
  statement: m <= n
  proof: by
  simpa using Fintype.card_le_of_injective f hf

中文:
定理 le_of_injective
  条件: (f : Fin m -> Fin n) (hf : f.Injective)
  结论: m <= n
  证明: by
  simpa using Fintype.card_le_of_injective f hf

Depends on / 依赖: Fintype, Fintype.card_le_of_injective, card_le_of_injective
-/
theorem le_of_injective (f : Fin m -> Fin n) (hf : f.Injective) : m <= n := by
  simpa using Fintype.card_le_of_injective f hf

/--
theorem `le_of_embedding` / 定理 `le_of_embedding`

English:
theorem le_of_embedding
  given: (f : Fin m ↪ Fin n)
  statement: m <= n
  proof: by
  simpa using Fintype.card_le_of_embedding f

中文:
定理 le_of_embedding
  条件: (f : Fin m ↪ Fin n)
  结论: m <= n
  证明: by
  simpa using Fintype.card_le_of_embedding f

Depends on / 依赖: Fintype, Fintype.card_le_of_embedding, card_le_of_embedding
-/
theorem le_of_embedding (f : Fin m ↪ Fin n) : m <= n := by
  simpa using Fintype.card_le_of_embedding f

/--
theorem `lt_of_injective_of_notMem` / 定理 `lt_of_injective_of_notMem`

English:
theorem lt_of_injective_of_notMem
  statement: (f : Fin m -> Fin n) (hf : f.Injective) {b : Fin n}
  proof: by
  simpa using Fintype.card_lt_of_injective_of_notMem f hf hb

中文:
定理 lt_of_injective_of_notMem
  结论: (f : Fin m -> Fin n) (hf : f.Injective) {b : Fin n}
  证明: by
  simpa using Fintype.card_lt_of_injective_of_notMem f hf hb

Depends on / 依赖: Fintype, Fintype.card_lt_of_injective_of_notMem, card_lt_of_injective_of_notMem
-/
theorem lt_of_injective_of_notMem (f : Fin m -> Fin n) (hf : f.Injective) {b : Fin n}
    (hb : b ∉ Set.range f) : m < n := by
  simpa using Fintype.card_lt_of_injective_of_notMem f hf hb

/--
theorem `le_of_surjective` / 定理 `le_of_surjective`

English:
theorem le_of_surjective
  given: (f : Fin m -> Fin n) (hf : Function.Surjective f)
  statement: n <= m
  proof: by
  simpa using Fintype.card_le_of_surjective f hf

中文:
定理 le_of_surjective
  条件: (f : Fin m -> Fin n) (hf : Function.Surjective f)
  结论: n <= m
  证明: by
  simpa using Fintype.card_le_of_surjective f hf

Depends on / 依赖: Fintype, Fintype.card_le_of_surjective, card_le_of_surjective
-/
theorem le_of_surjective (f : Fin m -> Fin n) (hf : Function.Surjective f) : n <= m := by
  simpa using Fintype.card_le_of_surjective f hf

/--
theorem `card_range_le` / 定理 `card_range_le`

English:
theorem card_range_le
  given: {α : Type*} [Fintype α] [DecidableEq α] (f : Fin m -> α)
  proof: by
  simpa using Fintype.card_range_le f

中文:
定理 card_range_le
  条件: {α : 类型} [Fintype α] [DecidableEq α] (f : Fin m -> α)
  证明: by
  simpa using Fintype.card_range_le f

Depends on / 依赖: Fintype, Fintype.card_range_le, card_range_le
-/
theorem card_range_le {α : Type*} [Fintype α] [DecidableEq α] (f : Fin m -> α) :
    Fintype.card (Set.range f) <= m := by
  simpa using Fintype.card_range_le f

end Fin
