/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Image
public import Mathlib.Order.TypeTags

/-! # `Set.range` on `WithBot` and `WithTop` -/

public section

open Set

variable {α β : Type*}

/--
theorem `WithBot.range_eq` / 定理 `WithBot.range_eq`

English:
theorem WithBot.range_eq
  given: (f : WithBot α -> β)
  proof: Option.range_eq f

中文:
定理 WithBot.range_eq
  条件: (f : WithBot α -> β)
  证明: Option.range_eq f

Depends on / 依赖: Option.range_eq, range_eq
-/
theorem WithBot.range_eq (f : WithBot α -> β) :
    range f = insert (f ⊥) (range (f ∘ WithBot.some : α -> β)) :=
  Option.range_eq f

/--
theorem `WithTop.range_eq` / 定理 `WithTop.range_eq`

English:
theorem WithTop.range_eq
  given: (f : WithTop α -> β)
  proof: Option.range_eq f

中文:
定理 WithTop.range_eq
  条件: (f : WithTop α -> β)
  证明: Option.range_eq f

Depends on / 依赖: Option.range_eq, range_eq
-/
theorem WithTop.range_eq (f : WithTop α -> β) :
    range f = insert (f ⊤) (range (f ∘ WithBot.some : α -> β)) :=
  Option.range_eq f
