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

/-
**WithBot.range_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithBot.range_eq (f : WithBot α -> β) : range f = insert (f ⊥) (range (f ∘
 WithBot.some : α -> β))
参数：f : WithBot α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.range_eq`：range_eq {α β} (f : Option α -> β) : range f = insert (
f none) (range (f ∘ some))
-/
theorem WithBot.range_eq (f : WithBot α → β) :
    range f = insert (f ⊥) (range (f ∘ WithBot.some : α → β)) :=
  Option.range_eq f
/-
**WithTop.range_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithTop.range_eq (f : WithTop α -> β) : range f = insert (f ⊤) (range (f ∘
 WithBot.some : α -> β))
参数：f : WithTop α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.range_eq`：range_eq {α β} (f : Option α -> β) : range f = insert (
f none) (range (f ∘ some))
-/
theorem WithTop.range_eq (f : WithTop α → β) :
    range f = insert (f ⊤) (range (f ∘ WithBot.some : α → β)) :=
  Option.range_eq f
