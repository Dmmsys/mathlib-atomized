/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Order.Interval.Basic
public import Mathlib.Data.Prod.Lex
public import Mathlib.Tactic.FastInstance
meta import Mathlib.Order.Interval.Basic -- shake: keep (for `#eval` testing)
meta import Mathlib.Order.Lex -- shake: keep (for `#eval` testing)

/-!
# The lexicographic order on intervals

This order is compatible with the inclusion ordering, but is total.

Under this ordering, `[(3, 3), (2, 2), (2, 3), (1, 1), (1, 2), (1, 3)]` is sorted.
-/

public section

namespace NonemptyInterval

variable {α}

section LELT
variable [LT α] [LE α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE (Lex (NonemptyInterval α))
  body: toLex (ofLex x).toDualProd <= toLex (ofLex y).toDualProd

中文:
实例 :
  签名: LE (Lex (Nonempty整数erval α))
  定义体: toLex (ofLex x).toDualProd <= toLex (ofLex y).toDualProd

Depends on / 依赖: toDualProd
-/
instance : LE (Lex (NonemptyInterval α)) where
  le x y := toLex (ofLex x).toDualProd <= toLex (ofLex y).toDualProd

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LT (Lex (NonemptyInterval α))
  body: toLex (ofLex x).toDualProd < toLex (ofLex y).toDualProd

中文:
实例 :
  签名: LT (Lex (Nonempty整数erval α))
  定义体: toLex (ofLex x).toDualProd < toLex (ofLex y).toDualProd

Depends on / 依赖: toDualProd
-/
instance : LT (Lex (NonemptyInterval α)) where
  lt x y := toLex (ofLex x).toDualProd < toLex (ofLex y).toDualProd

/--
theorem `toLex_le_toLex` / 定理 `toLex_le_toLex`

English:
theorem toLex_le_toLex
  given: {x y : NonemptyInterval α}
  proof: Prod.lex_def

中文:
定理 toLex_le_toLex
  条件: {x y : Nonempty整数erval α}
  证明: Prod.lex_def

Depends on / 依赖: Prod.lex_def, lex_def
-/
theorem toLex_le_toLex {x y : NonemptyInterval α} :
    toLex x <= toLex y ↔ y.fst < x.fst ∨ x.fst = y.fst ∧ x.snd <= y.snd :=
  Prod.lex_def

/--
theorem `toLex_lt_toLex` / 定理 `toLex_lt_toLex`

English:
theorem toLex_lt_toLex
  given: {x y : NonemptyInterval α}
  proof: Prod.lex_def

中文:
定理 toLex_lt_toLex
  条件: {x y : Nonempty整数erval α}
  证明: Prod.lex_def

Depends on / 依赖: Prod.lex_def, lex_def
-/
theorem toLex_lt_toLex {x y : NonemptyInterval α} :
    toLex x < toLex y ↔ y.fst < x.fst ∨ x.fst = y.fst ∧ x.snd < y.snd :=
  Prod.lex_def

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] [DecidableLT α] [DecidableLE α] : DecidableLE (Lex (NonemptyInterval α))
  body: fun _ _ => decidable_of_iff' _ toLex_le_toLex

中文:
实例 [DecidableEq
  签名: α] [DecidableLT α] [DecidableLE α] : DecidableLE (Lex (Nonempty整数erval α))
  定义体: fun _ _ => decidable_of_iff' _ toLex_le_toLex

Depends on / 依赖: decidable_of_iff, toLex_le_toLex
-/
instance [DecidableEq α] [DecidableLT α] [DecidableLE α] : DecidableLE (Lex (NonemptyInterval α)) :=
  fun _ _ => decidable_of_iff' _ toLex_le_toLex

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] [DecidableLT α] : DecidableLT (Lex (NonemptyInterval α))
  body: fun _ _ => decidable_of_iff' _ toLex_lt_toLex

中文:
实例 [DecidableEq
  签名: α] [DecidableLT α] : DecidableLT (Lex (Nonempty整数erval α))
  定义体: fun _ _ => decidable_of_iff' _ toLex_lt_toLex

Depends on / 依赖: decidable_of_iff, toLex_lt_toLex
-/
instance [DecidableEq α] [DecidableLT α] : DecidableLT (Lex (NonemptyInterval α)) :=
  fun _ _ => decidable_of_iff' _ toLex_lt_toLex

-- Sanity check on the ordering.
/-- info: [(3, 3), (2, 2), (2, 3), (1, 1), (1, 2), (1, 3)] -/
#guard_msgs in
#eval [
  NonemptyInterval.mk (1, 1) (by grind),
  NonemptyInterval.mk (1, 2) (by grind),
  NonemptyInterval.mk (1, 3) (by grind),
  NonemptyInterval.mk (2, 2) (by grind),
  NonemptyInterval.mk (2, 3) (by grind),
  NonemptyInterval.mk (3, 3) (by grind)].map toLex |>.mergeSort.map (·.toProd)

end LELT

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] : Preorder (Lex (NonemptyInterval α))
  body: fast_instance%
  Preorder.lift fun x => toLex (ofLex x).toDualProd

中文:
实例 [预序
  签名: α] : 预序 (Lex (Nonempty整数erval α))
  定义体: fast_instance%
  Preorder.lift fun x => toLex (ofLex x).toDualProd

Depends on / 依赖: fast_instance
-/
instance [Preorder α] : Preorder (Lex (NonemptyInterval α)) := fast_instance%
  Preorder.lift fun x => toLex (ofLex x).toDualProd

/--
theorem `toLex_mono` / 定理 `toLex_mono`

English:
theorem toLex_mono
  given: [PartialOrder α]
  statement: Monotone (toLex : NonemptyInterval α -> _)
  proof: Prod.Lex.toLex_mono.comp toDualProd_mono

中文:
定理 toLex_mono
  条件: [偏序 α]
  结论: 递增 (toLex : Nonempty整数erval α -> _)
  证明: Prod.Lex.toLex_mono.comp toDualProd_mono

Depends on / 依赖: Prod.Lex.toLex_mono.comp, toDualProd_mono, toLex_mono
-/
theorem toLex_mono [PartialOrder α] : Monotone (toLex : NonemptyInterval α -> _) :=
  Prod.Lex.toLex_mono.comp toDualProd_mono

/--
theorem `toLex_strictMono` / 定理 `toLex_strictMono`

English:
theorem toLex_strictMono
  given: [PartialOrder α]
  statement: StrictMono (toLex : NonemptyInterval α -> _)
  proof: Prod.Lex.toLex_strictMono.comp toDualProd_strictMono

中文:
定理 toLex_strictMono
  条件: [偏序 α]
  结论: 严格递增 (toLex : Nonempty整数erval α -> _)
  证明: Prod.Lex.toLex_strictMono.comp toDualProd_strictMono

Depends on / 依赖: Prod.Lex.toLex_strictMono.comp, toDualProd_strictMono, toLex_strictMono
-/
theorem toLex_strictMono [PartialOrder α] : StrictMono (toLex : NonemptyInterval α -> _) :=
  Prod.Lex.toLex_strictMono.comp toDualProd_strictMono

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PartialOrder
  signature: α] : PartialOrder (Lex (NonemptyInterval α))
  body: fast_instance%
PartialOrder.lift (fun x => toLex (ofLex x).toDualProd)
toLex.injective.comp toDualProd_injective.comp ofLex.injective

中文:
实例 [偏序
  签名: α] : 偏序 (Lex (Nonempty整数erval α))
  定义体: fast_instance%
PartialOrder.lift (fun x => toLex (ofLex x).toDualProd)
toLex.injective.comp toDualProd_injective.comp ofLex.injective

Depends on / 依赖: fast_instance
-/
instance [PartialOrder α] : PartialOrder (Lex (NonemptyInterval α)) := fast_instance%
PartialOrder.lift (fun x => toLex (ofLex x).toDualProd)
toLex.injective.comp toDualProd_injective.comp ofLex.injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LinearOrder
  signature: α] : LinearOrder (Lex (NonemptyInterval α))
  body: fast_instance%
  { LinearOrder.lift' (fun x : Lex (NonemptyInterval α) => toLex (ofLex x).toDualProd) <|
toLex.injective.comp toDualProd_injective.comp ofLex.injective with
    toDecidableEq := inferInstance
    toDecidableLT := inferInstance
    toDecidableLE := inferInstance }

中文:
实例 [线性序
  签名: α] : 线性序 (Lex (Nonempty整数erval α))
  定义体: fast_instance%
  { LinearOrder.lift' (fun x : Lex (NonemptyInterval α) => toLex (ofLex x).toDualProd) <|
toLex.injective.comp toDualProd_injective.comp ofLex.injective with
    toDecidableEq := inferInstance
    toDecidableLT := inferInstance
    toDecidableLE := inferInstance }

Depends on / 依赖: fast_instance
-/
instance [LinearOrder α] : LinearOrder (Lex (NonemptyInterval α)) := fast_instance%
  { LinearOrder.lift' (fun x : Lex (NonemptyInterval α) => toLex (ofLex x).toDualProd) <|
toLex.injective.comp toDualProd_injective.comp ofLex.injective with
    toDecidableEq := inferInstance
    toDecidableLT := inferInstance
    toDecidableLE := inferInstance }

end NonemptyInterval
