/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Order.TypeTags

/-!
# Fintype instances for `WithTop α` and `WithBot α`
-/

public section

variable {α : Type*}

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fintype
  signature: α] : Fintype (WithTop α)
  body: inferInstanceAs Fintype (Option α)

@[to_dual]

中文:
实例 [Fintype
  签名: α] : Fintype (WithTop α)
  定义体: inferInstanceAs Fintype (Option α)

@[to_dual]

Depends on / 依赖: Fintype
-/
instance [Fintype α] : Fintype (WithTop α) :=
inferInstanceAs Fintype (Option α)

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: α] : Finite (WithTop α)
  body: have := Fintype.ofFinite α
  Finite.of_fintype _

中文:
实例 [Finite
  签名: α] : Finite (WithTop α)
  定义体: have := Fintype.ofFinite α
  Finite.of_fintype _

Depends on / 依赖: Finite, Finite.of_fintype, Fintype, Fintype.ofFinite, ofFinite, of_fintype
-/
instance [Finite α] : Finite (WithTop α) :=
  have := Fintype.ofFinite α
  Finite.of_fintype _
