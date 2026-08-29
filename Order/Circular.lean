/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Lattice
public import Mathlib.Tactic.Order

/-!
# Circular order hierarchy

This file defines circular preorders, circular partial orders and circular orders.

## Hierarchy

* A ternary "betweenness" relation `btw : α → α → α → Prop` forms a `CircularOrder` if it is
  - reflexive: `btw a a a`
  - cyclic: `btw a b c → btw b c a`
  - antisymmetric: `btw a b c → btw c b a → a = b ∨ b = c ∨ c = a`
  - total: `btw a b c ∨ btw c b a`

  along with a strict betweenness relation `sbtw : α → α → α → Prop` which respects
  `sbtw a b c ↔ btw a b c ∧ ¬ btw c b a`, analogously to how `<` and `≤` are related, and is
  - transitive: `sbtw a b c → sbtw b d c → sbtw a d c`.

* A `CircularPartialOrder` drops totality.

* A `CircularPreorder` further drops antisymmetry.

The intuition is that a circular order is a circle and `btw a b c` means that going around
clockwise from `a` you reach `b` before `c` (`b` is between `a` and `c` is meaningless on an
unoriented circle). A circular partial order is several, potentially intersecting, circles. A
circular preorder is like a circular partial order, but several points can coexist.

Note that the relations between `CircularPreorder`, `CircularPartialOrder` and `CircularOrder`
are subtler than between `Preorder`, `PartialOrder`, `LinearOrder`. In particular, one cannot
simply extend the `Btw` of a `CircularPartialOrder` to make it a `CircularOrder`.

One can translate from usual orders to circular ones by "closing the necklace at infinity". See
`LE.toBtw` and `LT.toSBtw`. Going the other way involves "cutting the necklace" or
"rolling the necklace open".

## Examples

Some concrete circular orders one encounters in the wild are `ZMod n` for `0 < n`, `Circle`,
`Real.Angle`...

## Main definitions

* `Set.cIcc`: Closed-closed circular interval.
* `Set.cIoo`: Open-open circular interval.

## Notes

There's an unsolved diamond on `OrderDual α` here. The instances `LE α → Btw αᵒᵈ` and
`LT α → SBtw αᵒᵈ` can each be inferred in two ways:
* `LE α` → `Btw α` → `Btw αᵒᵈ` vs
  `LE α` → `LE αᵒᵈ` → `Btw αᵒᵈ`
* `LT α` → `SBtw α` → `SBtw αᵒᵈ` vs
  `LT α` → `LT αᵒᵈ` → `SBtw αᵒᵈ`

The fields are propeq, but not defeq. It is temporarily fixed by turning the circularizing instances
into definitions.

## TODO

Antisymmetry is quite weak in the sense that there's no way to discriminate which two points are
equal. This prevents defining closed-open intervals `cIco` and `cIoc` in the neat `=`-less way. We
currently haven't defined them at all.

What is the correct generality of "rolling the necklace" open? At least, this works for `α × β` and
`β × α` where `α` is a circular order and `β` is a linear order.

What's next is to define circular groups and provide instances for `ZMod n`, the usual circle group
`Circle`, and `RootsOfUnity M`. What conditions do we need on `M` for this last one
to work?

We should have circular order homomorphisms. The typical example is
`daysToMonth : DaysOfTheYear →c MonthsOfTheYear` which relates the circular order of days
and the circular order of months. Is `α →c β` a good notation?

## References

* https://en.wikipedia.org/wiki/Cyclic_order
* https://en.wikipedia.org/wiki/Partial_cyclic_order

## Tags

circular order, cyclic order, circularly ordered set, cyclically ordered set
-/

@[expose] public section

assert_not_exists RelIso

/--
Definition of `Btw` / `Btw` 的定义

English:
class Btw
  parameters: (α : Type*)
  axioms and operations (1):
    - btw : α -> α -> α -> Prop

中文:
类 Btw
  参数: (α : 类型)
  公理与运算 (1 个):
    - btw : α -> α -> α -> 命题
-/
class Btw (α : Type*) where
  /-- Betweenness for circular orders. `btw a b c` states that `b` is between `a` and `c` (in that
  order). -/
  btw : α -> α -> α -> Prop

export Btw (btw)

/--
Definition of `SBtw` / `SBtw` 的定义

English:
class SBtw
  parameters: (α : Type*)
  axioms and operations (1):
    - sbtw : α -> α -> α -> Prop

中文:
类 SBtw
  参数: (α : 类型)
  公理与运算 (1 个):
    - sbtw : α -> α -> α -> 命题
-/
class SBtw (α : Type*) where
  /-- Strict betweenness for circular orders. `sbtw a b c` states that `b` is strictly between `a`
  and `c` (in that order). -/
  sbtw : α -> α -> α -> Prop

export SBtw (sbtw)

/--
Definition of `CircularPreorder` / `CircularPreorder` 的定义

English:
class CircularPreorder
  parameters: (α : Type*)
  extends: Btw α, SBtw α
  axioms and operations (5):
    - btw_refl((a : α)) : btw a a a
    - btw_cyclic_left({a b c : α}) : btw a b c -> btw b c a
    - sbtw : = fun a b c => btw a b c ∧ ¬btw c b a
    - sbtw_iff_btw_not_btw({a b c : α}) : sbtw a b c ↔ btw a b c ∧ ¬btw c b a  [default: by intros; rfl]
    - sbtw_trans_left({a b c d : α}) : sbtw a b c -> sbtw b d c -> sbtw a d c

中文:
类 CircularPreorder
  参数: (α : 类型)
  继承: Btw α, SBtw α
  公理与运算 (5 个):
    - btw_refl((a : α)) : btw a a a
    - btw_cyclic_left({a b c : α}) : btw a b c -> btw b c a
    - sbtw : = fun a b c => btw a b c ∧ ¬btw c b a
    - sbtw_iff_btw_not_btw({a b c : α}) : sbtw a b c ↔ btw a b c ∧ ¬btw c b a  [默认: by intros; rfl]
    - sbtw_trans_left({a b c d : α}) : sbtw a b c -> sbtw b d c -> sbtw a d c
-/
class CircularPreorder (α : Type*) extends Btw α, SBtw α where
  /-- `a` is between `a` and `a`. -/
  btw_refl (a : α) : btw a a a
  /-- If `b` is between `a` and `c`, then `c` is between `b` and `a`.
  This is motivated by imagining three points on a circle. -/
  btw_cyclic_left {a b c : α} : btw a b c -> btw b c a
  sbtw := fun a b c => btw a b c ∧ ¬btw c b a
  /-- Strict betweenness is given by betweenness in one direction and non-betweenness in the other.

  I.e., if `b` is between `a` and `c` but not between `c` and `a`, then we say `b` is strictly
  between `a` and `c`. -/
  sbtw_iff_btw_not_btw {a b c : α} : sbtw a b c ↔ btw a b c ∧ ¬btw c b a := by intros; rfl
  /-- For any fixed `c`, `fun a b ↦ sbtw a b c` is a transitive relation.

  I.e., given `a` `b` `d` `c` in that "order", if we have `b` strictly between `a` and `c`, and `d`
  strictly between `b` and `c`, then `d` is strictly between `a` and `c`. -/
  sbtw_trans_left {a b c d : α} : sbtw a b c -> sbtw b d c -> sbtw a d c

export CircularPreorder (btw_refl btw_cyclic_left sbtw_trans_left)

/--
Definition of `CircularPartialOrder` / `CircularPartialOrder` 的定义

English:
class CircularPartialOrder
  parameters: (α : Type*)
  extends: CircularPreorder α
  axioms and operations (1):
    - btw_antisymm({a b c : α}) : btw a b c -> btw c b a -> a = b ∨ b = c ∨ c = a

中文:
类 CircularPartialOrder
  参数: (α : 类型)
  继承: CircularPreorder α
  公理与运算 (1 个):
    - btw_antisymm({a b c : α}) : btw a b c -> btw c b a -> a = b ∨ b = c ∨ c = a
-/
class CircularPartialOrder (α : Type*) extends CircularPreorder α where
  /-- If `b` is between `a` and `c` and also between `c` and `a`, then at least one pair of points
  among `a`, `b`, `c` are identical. -/
  btw_antisymm {a b c : α} : btw a b c -> btw c b a -> a = b ∨ b = c ∨ c = a

export CircularPartialOrder (btw_antisymm)

/--
Definition of `CircularOrder` / `CircularOrder` 的定义

English:
class CircularOrder
  parameters: (α : Type*)
  extends: CircularPartialOrder α
  axioms and operations (1):
    - btw_total : forall a b c : α, btw a b c ∨ btw c b a

中文:
类 CircularOrder
  参数: (α : 类型)
  继承: CircularPartialOrder α
  公理与运算 (1 个):
    - btw_total : 对任意 a b c : α, btw a b c ∨ btw c b a
-/
class CircularOrder (α : Type*) extends CircularPartialOrder α where
  /-- For any triple of points, the second is between the other two one way or another. -/
  btw_total : forall a b c : α, btw a b c ∨ btw c b a

export CircularOrder (btw_total)

/-! ### Circular preorders -/


section CircularPreorder

variable {α : Type*} [CircularPreorder α]

/--
theorem `btw_rfl` / 定理 `btw_rfl`

English:
theorem btw_rfl
  given: {a : α}
  statement: btw a a a
  proof: btw_refl _

中文:
定理 btw_rfl
  条件: {a : α}
  结论: btw a a a
  证明: btw_refl _

Depends on / 依赖: btw_refl
-/
theorem btw_rfl {a : α} : btw a a a :=
  btw_refl _

-- TODO: `alias` creates a def instead of a lemma (because `btw_cyclic_left` is a def).
-- alias btw_cyclic_left ← Btw.btw.cyclic_left
/--
theorem `Btw.btw.cyclic_left` / 定理 `Btw.btw.cyclic_left`

English:
theorem Btw.btw.cyclic_left
  given: {a b c : α} (h : btw a b c)
  statement: btw b c a
  proof: btw_cyclic_left h

中文:
定理 Btw.btw.cyclic_left
  条件: {a b c : α} (h : btw a b c)
  结论: btw b c a
  证明: btw_cyclic_left h

Depends on / 依赖: btw_cyclic_left
-/
theorem Btw.btw.cyclic_left {a b c : α} (h : btw a b c) : btw b c a :=
  btw_cyclic_left h

/--
theorem `btw_cyclic_right` / 定理 `btw_cyclic_right`

English:
theorem btw_cyclic_right
  given: {a b c : α} (h : btw a b c)
  statement: btw c a b
  proof: h.cyclic_left.cyclic_left

alias Btw.btw.cyclic_right := btw_cyclic_right

中文:
定理 btw_cyclic_right
  条件: {a b c : α} (h : btw a b c)
  结论: btw c a b
  证明: h.cyclic_left.cyclic_left

alias Btw.btw.cyclic_right := btw_cyclic_right

Depends on / 依赖: cyclic_left, h.cyclic_left.cyclic_left
-/
theorem btw_cyclic_right {a b c : α} (h : btw a b c) : btw c a b :=
  h.cyclic_left.cyclic_left

alias Btw.btw.cyclic_right := btw_cyclic_right

/--
theorem `btw_cyclic` / 定理 `btw_cyclic`

English:
theorem btw_cyclic
  given: {a b c : α}
  statement: btw a b c ↔ btw c a b
  proof: ⟨btw_cyclic_right, btw_cyclic_left⟩

中文:
定理 btw_cyclic
  条件: {a b c : α}
  结论: btw a b c ↔ btw c a b
  证明: ⟨btw_cyclic_right, btw_cyclic_left⟩

Depends on / 依赖: btw_cyclic_left, btw_cyclic_right
-/
theorem btw_cyclic {a b c : α} : btw a b c ↔ btw c a b :=
  ⟨btw_cyclic_right, btw_cyclic_left⟩

/--
theorem `sbtw_iff_btw_not_btw` / 定理 `sbtw_iff_btw_not_btw`

English:
theorem sbtw_iff_btw_not_btw
  given: {a b c : α}
  statement: sbtw a b c ↔ btw a b c ∧ ¬btw c b a
  proof: CircularPreorder.sbtw_iff_btw_not_btw

中文:
定理 sbtw_iff_btw_not_btw
  条件: {a b c : α}
  结论: sbtw a b c ↔ btw a b c ∧ ¬btw c b a
  证明: CircularPreorder.sbtw_iff_btw_not_btw

Depends on / 依赖: CircularPreorder, CircularPreorder.sbtw_iff_btw_not_btw, sbtw_iff_btw_not_btw
-/
theorem sbtw_iff_btw_not_btw {a b c : α} : sbtw a b c ↔ btw a b c ∧ ¬btw c b a :=
  CircularPreorder.sbtw_iff_btw_not_btw

/--
theorem `btw_of_sbtw` / 定理 `btw_of_sbtw`

English:
theorem btw_of_sbtw
  given: {a b c : α} (h : sbtw a b c)
  statement: btw a b c
  proof: (sbtw_iff_btw_not_btw.1 h).1

alias SBtw.sbtw.btw := btw_of_sbtw

中文:
定理 btw_of_sbtw
  条件: {a b c : α} (h : sbtw a b c)
  结论: btw a b c
  证明: (sbtw_iff_btw_not_btw.1 h).1

alias SBtw.sbtw.btw := btw_of_sbtw

Depends on / 依赖: sbtw_iff_btw_not_btw
-/
theorem btw_of_sbtw {a b c : α} (h : sbtw a b c) : btw a b c :=
  (sbtw_iff_btw_not_btw.1 h).1

alias SBtw.sbtw.btw := btw_of_sbtw

/--
theorem `not_btw_of_sbtw` / 定理 `not_btw_of_sbtw`

English:
theorem not_btw_of_sbtw
  given: {a b c : α} (h : sbtw a b c)
  statement: ¬btw c b a
  proof: (sbtw_iff_btw_not_btw.1 h).2

alias SBtw.sbtw.not_btw := not_btw_of_sbtw

中文:
定理 not_btw_of_sbtw
  条件: {a b c : α} (h : sbtw a b c)
  结论: ¬btw c b a
  证明: (sbtw_iff_btw_not_btw.1 h).2

alias SBtw.sbtw.not_btw := not_btw_of_sbtw

Depends on / 依赖: sbtw_iff_btw_not_btw
-/
theorem not_btw_of_sbtw {a b c : α} (h : sbtw a b c) : ¬btw c b a :=
  (sbtw_iff_btw_not_btw.1 h).2

alias SBtw.sbtw.not_btw := not_btw_of_sbtw

/--
theorem `not_sbtw_of_btw` / 定理 `not_sbtw_of_btw`

English:
theorem not_sbtw_of_btw
  given: {a b c : α} (h : btw a b c)
  statement: ¬sbtw c b a
  proof: fun h' => h'.not_btw h

alias Btw.btw.not_sbtw := not_sbtw_of_btw

中文:
定理 not_sbtw_of_btw
  条件: {a b c : α} (h : btw a b c)
  结论: ¬sbtw c b a
  证明: fun h' => h'.not_btw h

alias Btw.btw.not_sbtw := not_sbtw_of_btw

Depends on / 依赖: not_btw
-/
theorem not_sbtw_of_btw {a b c : α} (h : btw a b c) : ¬sbtw c b a := fun h' => h'.not_btw h

alias Btw.btw.not_sbtw := not_sbtw_of_btw

/--
theorem `sbtw_of_btw_not_btw` / 定理 `sbtw_of_btw_not_btw`

English:
theorem sbtw_of_btw_not_btw
  given: {a b c : α} (habc : btw a b c) (hcba : ¬btw c b a)
  statement: sbtw a b c
  proof: sbtw_iff_btw_not_btw.2 ⟨habc, hcba⟩

alias Btw.btw.sbtw_of_not_btw := sbtw_of_btw_not_btw

中文:
定理 sbtw_of_btw_not_btw
  条件: {a b c : α} (habc : btw a b c) (hcba : ¬btw c b a)
  结论: sbtw a b c
  证明: sbtw_iff_btw_not_btw.2 ⟨habc, hcba⟩

alias Btw.btw.sbtw_of_not_btw := sbtw_of_btw_not_btw

Depends on / 依赖: sbtw_iff_btw_not_btw
-/
theorem sbtw_of_btw_not_btw {a b c : α} (habc : btw a b c) (hcba : ¬btw c b a) : sbtw a b c :=
  sbtw_iff_btw_not_btw.2 ⟨habc, hcba⟩

alias Btw.btw.sbtw_of_not_btw := sbtw_of_btw_not_btw

/--
theorem `sbtw_cyclic_left` / 定理 `sbtw_cyclic_left`

English:
theorem sbtw_cyclic_left
  given: {a b c : α} (h : sbtw a b c)
  statement: sbtw b c a
  proof: h.btw.cyclic_left.sbtw_of_not_btw fun h' => h.not_btw h'.cyclic_left

alias SBtw.sbtw.cyclic_left := sbtw_cyclic_left

中文:
定理 sbtw_cyclic_left
  条件: {a b c : α} (h : sbtw a b c)
  结论: sbtw b c a
  证明: h.btw.cyclic_left.sbtw_of_not_btw fun h' => h.not_btw h'.cyclic_left

alias SBtw.sbtw.cyclic_left := sbtw_cyclic_left

Depends on / 依赖: cyclic_left, h.btw.cyclic_left.sbtw_of_not_btw, h.not_btw, not_btw, sbtw_of_not_btw
-/
theorem sbtw_cyclic_left {a b c : α} (h : sbtw a b c) : sbtw b c a :=
  h.btw.cyclic_left.sbtw_of_not_btw fun h' => h.not_btw h'.cyclic_left

alias SBtw.sbtw.cyclic_left := sbtw_cyclic_left

/--
theorem `sbtw_cyclic_right` / 定理 `sbtw_cyclic_right`

English:
theorem sbtw_cyclic_right
  given: {a b c : α} (h : sbtw a b c)
  statement: sbtw c a b
  proof: h.cyclic_left.cyclic_left

alias SBtw.sbtw.cyclic_right := sbtw_cyclic_right

中文:
定理 sbtw_cyclic_right
  条件: {a b c : α} (h : sbtw a b c)
  结论: sbtw c a b
  证明: h.cyclic_left.cyclic_left

alias SBtw.sbtw.cyclic_right := sbtw_cyclic_right

Depends on / 依赖: cyclic_left, h.cyclic_left.cyclic_left
-/
theorem sbtw_cyclic_right {a b c : α} (h : sbtw a b c) : sbtw c a b :=
  h.cyclic_left.cyclic_left

alias SBtw.sbtw.cyclic_right := sbtw_cyclic_right

/--
theorem `sbtw_cyclic` / 定理 `sbtw_cyclic`

English:
theorem sbtw_cyclic
  given: {a b c : α}
  statement: sbtw a b c ↔ sbtw c a b
  proof: ⟨sbtw_cyclic_right, sbtw_cyclic_left⟩

中文:
定理 sbtw_cyclic
  条件: {a b c : α}
  结论: sbtw a b c ↔ sbtw c a b
  证明: ⟨sbtw_cyclic_right, sbtw_cyclic_left⟩

Depends on / 依赖: sbtw_cyclic_left, sbtw_cyclic_right
-/
theorem sbtw_cyclic {a b c : α} : sbtw a b c ↔ sbtw c a b :=
  ⟨sbtw_cyclic_right, sbtw_cyclic_left⟩

-- TODO: `alias` creates a def instead of a lemma (because `sbtw_trans_left` is a def).
-- alias btw_trans_left ← SBtw.sbtw.trans_left
/--
theorem `SBtw.sbtw.trans_left` / 定理 `SBtw.sbtw.trans_left`

English:
theorem SBtw.sbtw.trans_left
  given: {a b c d : α} (h : sbtw a b c)
  statement: sbtw b d c -> sbtw a d c
  proof: sbtw_trans_left h

中文:
定理 SBtw.sbtw.trans_left
  条件: {a b c d : α} (h : sbtw a b c)
  结论: sbtw b d c -> sbtw a d c
  证明: sbtw_trans_left h

Depends on / 依赖: sbtw_trans_left
-/
theorem SBtw.sbtw.trans_left {a b c d : α} (h : sbtw a b c) : sbtw b d c -> sbtw a d c :=
  sbtw_trans_left h

/--
theorem `sbtw_trans_right` / 定理 `sbtw_trans_right`

English:
theorem sbtw_trans_right
  given: {a b c d : α} (hbc : sbtw a b c) (hcd : sbtw a c d)
  statement: sbtw a b d
  proof: (hbc.cyclic_left.trans_left hcd.cyclic_left).cyclic_right

alias SBtw.sbtw.trans_right := sbtw_trans_right

中文:
定理 sbtw_trans_right
  条件: {a b c d : α} (hbc : sbtw a b c) (hcd : sbtw a c d)
  结论: sbtw a b d
  证明: (hbc.cyclic_left.trans_left hcd.cyclic_left).cyclic_right

alias SBtw.sbtw.trans_right := sbtw_trans_right

Depends on / 依赖: cyclic_left, cyclic_right, hbc.cyclic_left.trans_left, hcd.cyclic_left, trans_left
-/
theorem sbtw_trans_right {a b c d : α} (hbc : sbtw a b c) (hcd : sbtw a c d) : sbtw a b d :=
  (hbc.cyclic_left.trans_left hcd.cyclic_left).cyclic_right

alias SBtw.sbtw.trans_right := sbtw_trans_right

/--
theorem `sbtw_asymm` / 定理 `sbtw_asymm`

English:
theorem sbtw_asymm
  given: {a b c : α} (h : sbtw a b c)
  statement: ¬sbtw c b a
  proof: h.btw.not_sbtw

alias SBtw.sbtw.not_sbtw := sbtw_asymm

中文:
定理 sbtw_asymm
  条件: {a b c : α} (h : sbtw a b c)
  结论: ¬sbtw c b a
  证明: h.btw.not_sbtw

alias SBtw.sbtw.not_sbtw := sbtw_asymm

Depends on / 依赖: h.btw.not_sbtw, not_sbtw
-/
theorem sbtw_asymm {a b c : α} (h : sbtw a b c) : ¬sbtw c b a :=
  h.btw.not_sbtw

alias SBtw.sbtw.not_sbtw := sbtw_asymm

/--
theorem `sbtw_irrefl_left_right` / 定理 `sbtw_irrefl_left_right`

English:
theorem sbtw_irrefl_left_right
  given: {a b : α}
  statement: ¬sbtw a b a
  proof: fun h => h.not_btw h.btw

中文:
定理 sbtw_irrefl_left_right
  条件: {a b : α}
  结论: ¬sbtw a b a
  证明: fun h => h.not_btw h.btw

Depends on / 依赖: h.btw, h.not_btw, not_btw
-/
theorem sbtw_irrefl_left_right {a b : α} : ¬sbtw a b a := fun h => h.not_btw h.btw

/--
theorem `sbtw_irrefl_left` / 定理 `sbtw_irrefl_left`

English:
theorem sbtw_irrefl_left
  given: {a b : α}
  statement: ¬sbtw a a b
  proof: fun h => sbtw_irrefl_left_right h.cyclic_left

中文:
定理 sbtw_irrefl_left
  条件: {a b : α}
  结论: ¬sbtw a a b
  证明: fun h => sbtw_irrefl_left_right h.cyclic_left

Depends on / 依赖: cyclic_left, h.cyclic_left, sbtw_irrefl_left_right
-/
theorem sbtw_irrefl_left {a b : α} : ¬sbtw a a b := fun h => sbtw_irrefl_left_right h.cyclic_left

/--
theorem `sbtw_irrefl_right` / 定理 `sbtw_irrefl_right`

English:
theorem sbtw_irrefl_right
  given: {a b : α}
  statement: ¬sbtw a b b
  proof: fun h => sbtw_irrefl_left_right h.cyclic_right

中文:
定理 sbtw_irrefl_right
  条件: {a b : α}
  结论: ¬sbtw a b b
  证明: fun h => sbtw_irrefl_left_right h.cyclic_right

Depends on / 依赖: cyclic_right, h.cyclic_right, sbtw_irrefl_left_right
-/
theorem sbtw_irrefl_right {a b : α} : ¬sbtw a b b := fun h => sbtw_irrefl_left_right h.cyclic_right

/--
theorem `sbtw_irrefl` / 定理 `sbtw_irrefl`

English:
theorem sbtw_irrefl
  given: (a : α)
  statement: ¬sbtw a a a
  proof: sbtw_irrefl_left_right

中文:
定理 sbtw_irrefl
  条件: (a : α)
  结论: ¬sbtw a a a
  证明: sbtw_irrefl_left_right

Depends on / 依赖: sbtw_irrefl_left_right
-/
theorem sbtw_irrefl (a : α) : ¬sbtw a a a :=
  sbtw_irrefl_left_right

end CircularPreorder

/-! ### Circular partial orders -/


section CircularPartialOrder

variable {α : Type*} [CircularPartialOrder α]

-- TODO: `alias` creates a def instead of a lemma (because `btw_antisymm` is a def).
-- alias btw_antisymm ← Btw.btw.antisymm
/--
theorem `Btw.btw.antisymm` / 定理 `Btw.btw.antisymm`

English:
theorem Btw.btw.antisymm
  given: {a b c : α} (h : btw a b c)
  statement: btw c b a -> a = b ∨ b = c ∨ c = a
  proof: btw_antisymm h

中文:
定理 Btw.btw.antisymm
  条件: {a b c : α} (h : btw a b c)
  结论: btw c b a -> a = b ∨ b = c ∨ c = a
  证明: btw_antisymm h

Depends on / 依赖: btw_antisymm
-/
theorem Btw.btw.antisymm {a b c : α} (h : btw a b c) : btw c b a -> a = b ∨ b = c ∨ c = a :=
  btw_antisymm h

end CircularPartialOrder

/-! ### Circular orders -/


section CircularOrder

variable {α : Type*} [CircularOrder α]

/--
theorem `btw_refl_left_right` / 定理 `btw_refl_left_right`

English:
theorem btw_refl_left_right
  given: (a b : α)
  statement: btw a b a
  proof: or_self_iff.1 (btw_total a b a)

中文:
定理 btw_refl_left_right
  条件: (a b : α)
  结论: btw a b a
  证明: or_self_iff.1 (btw_total a b a)

Depends on / 依赖: btw_total, or_self_iff
-/
theorem btw_refl_left_right (a b : α) : btw a b a :=
  or_self_iff.1 (btw_total a b a)

/--
theorem `btw_rfl_left_right` / 定理 `btw_rfl_left_right`

English:
theorem btw_rfl_left_right
  given: {a b : α}
  statement: btw a b a
  proof: btw_refl_left_right _ _

中文:
定理 btw_rfl_left_right
  条件: {a b : α}
  结论: btw a b a
  证明: btw_refl_left_right _ _

Depends on / 依赖: btw_refl_left_right
-/
theorem btw_rfl_left_right {a b : α} : btw a b a :=
  btw_refl_left_right _ _

/--
theorem `btw_refl_left` / 定理 `btw_refl_left`

English:
theorem btw_refl_left
  given: (a b : α)
  statement: btw a a b
  proof: btw_rfl_left_right.cyclic_right

中文:
定理 btw_refl_left
  条件: (a b : α)
  结论: btw a a b
  证明: btw_rfl_left_right.cyclic_right

Depends on / 依赖: btw_rfl_left_right, btw_rfl_left_right.cyclic_right, cyclic_right
-/
theorem btw_refl_left (a b : α) : btw a a b :=
  btw_rfl_left_right.cyclic_right

/--
theorem `btw_rfl_left` / 定理 `btw_rfl_left`

English:
theorem btw_rfl_left
  given: {a b : α}
  statement: btw a a b
  proof: btw_refl_left _ _

中文:
定理 btw_rfl_left
  条件: {a b : α}
  结论: btw a a b
  证明: btw_refl_left _ _

Depends on / 依赖: btw_refl_left
-/
theorem btw_rfl_left {a b : α} : btw a a b :=
  btw_refl_left _ _

/--
theorem `btw_refl_right` / 定理 `btw_refl_right`

English:
theorem btw_refl_right
  given: (a b : α)
  statement: btw a b b
  proof: btw_rfl_left_right.cyclic_left

中文:
定理 btw_refl_right
  条件: (a b : α)
  结论: btw a b b
  证明: btw_rfl_left_right.cyclic_left

Depends on / 依赖: btw_rfl_left_right, btw_rfl_left_right.cyclic_left, cyclic_left
-/
theorem btw_refl_right (a b : α) : btw a b b :=
  btw_rfl_left_right.cyclic_left

/--
theorem `btw_rfl_right` / 定理 `btw_rfl_right`

English:
theorem btw_rfl_right
  given: {a b : α}
  statement: btw a b b
  proof: btw_refl_right _ _

中文:
定理 btw_rfl_right
  条件: {a b : α}
  结论: btw a b b
  证明: btw_refl_right _ _

Depends on / 依赖: btw_refl_right
-/
theorem btw_rfl_right {a b : α} : btw a b b :=
  btw_refl_right _ _

/--
theorem `sbtw_iff_not_btw` / 定理 `sbtw_iff_not_btw`

English:
theorem sbtw_iff_not_btw
  given: {a b c : α}
  statement: sbtw a b c ↔ ¬btw c b a
  proof: by
  rw [sbtw_iff_btw_not_btw]
  exact and_iff_right_of_imp (btw_total _ _ _).resolve_left

中文:
定理 sbtw_iff_not_btw
  条件: {a b c : α}
  结论: sbtw a b c ↔ ¬btw c b a
  证明: by
  rw [sbtw_iff_btw_not_btw]
  exact and_iff_right_of_imp (btw_total _ _ _).resolve_left

Depends on / 依赖: and_iff_right_of_imp, btw_total, resolve_left, sbtw_iff_btw_not_btw
-/
theorem sbtw_iff_not_btw {a b c : α} : sbtw a b c ↔ ¬btw c b a := by
  rw [sbtw_iff_btw_not_btw]
  exact and_iff_right_of_imp (btw_total _ _ _).resolve_left

/--
theorem `btw_iff_not_sbtw` / 定理 `btw_iff_not_sbtw`

English:
theorem btw_iff_not_sbtw
  given: {a b c : α}
  statement: btw a b c ↔ ¬sbtw c b a
  proof: iff_not_comm.1 sbtw_iff_not_btw

中文:
定理 btw_iff_not_sbtw
  条件: {a b c : α}
  结论: btw a b c ↔ ¬sbtw c b a
  证明: iff_not_comm.1 sbtw_iff_not_btw

Depends on / 依赖: iff_not_comm, sbtw_iff_not_btw
-/
theorem btw_iff_not_sbtw {a b c : α} : btw a b c ↔ ¬sbtw c b a :=
  iff_not_comm.1 sbtw_iff_not_btw

end CircularOrder

/-! ### Circular intervals -/


namespace Set

section CircularPreorder

variable {α : Type*} [CircularPreorder α]

/--
Definition of `cIcc` / `cIcc` 的定义

English:
definition cIcc
  signature: (a b : α)
  body: { x | btw a x b }

中文:
定义 cIcc
  签名: (a b : α)
  定义体: { x | btw a x b }
-/
def cIcc (a b : α) : Set α :=
  { x | btw a x b }

/--
Definition of `cIoo` / `cIoo` 的定义

English:
definition cIoo
  signature: (a b : α)
  body: { x | sbtw a x b }

@[simp]

中文:
定义 cIoo
  签名: (a b : α)
  定义体: { x | sbtw a x b }

@[simp]
-/
def cIoo (a b : α) : Set α :=
  { x | sbtw a x b }

@[simp]
/--
theorem `mem_cIcc` / 定理 `mem_cIcc`

English:
theorem mem_cIcc
  given: {a b x : α}
  statement: x in cIcc a b ↔ btw a x b
  proof: Iff.rfl

@[simp]

中文:
定理 mem_cIcc
  条件: {a b x : α}
  结论: x in cIcc a b ↔ btw a x b
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_cIcc {a b x : α} : x in cIcc a b ↔ btw a x b :=
  Iff.rfl

@[simp]
/--
theorem `mem_cIoo` / 定理 `mem_cIoo`

English:
theorem mem_cIoo
  given: {a b x : α}
  statement: x in cIoo a b ↔ sbtw a x b
  proof: Iff.rfl

中文:
定理 mem_cIoo
  条件: {a b x : α}
  结论: x in cIoo a b ↔ sbtw a x b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_cIoo {a b x : α} : x in cIoo a b ↔ sbtw a x b :=
  Iff.rfl

end CircularPreorder

section CircularOrder

variable {α : Type*} [CircularOrder α]

/--
theorem `left_mem_cIcc` / 定理 `left_mem_cIcc`

English:
theorem left_mem_cIcc
  given: (a b : α)
  statement: a in cIcc a b
  proof: btw_rfl_left

中文:
定理 left_mem_cIcc
  条件: (a b : α)
  结论: a in cIcc a b
  证明: btw_rfl_left

Depends on / 依赖: btw_rfl_left
-/
theorem left_mem_cIcc (a b : α) : a in cIcc a b :=
  btw_rfl_left

/--
theorem `right_mem_cIcc` / 定理 `right_mem_cIcc`

English:
theorem right_mem_cIcc
  given: (a b : α)
  statement: b in cIcc a b
  proof: btw_rfl_right

中文:
定理 right_mem_cIcc
  条件: (a b : α)
  结论: b in cIcc a b
  证明: btw_rfl_right

Depends on / 依赖: btw_rfl_right
-/
theorem right_mem_cIcc (a b : α) : b in cIcc a b :=
  btw_rfl_right

/--
theorem `compl_cIcc` / 定理 `compl_cIcc`

English:
theorem compl_cIcc
  given: {a b : α}
  statement: (cIcc a b)ᶜ = cIoo b a
  proof: by
  ext
  rw [Set.mem_cIoo]; rw [sbtw_iff_not_btw]; rw [cIcc]; rw [mem_compl_iff]; rw [mem_ofPred]

中文:
定理 compl_cIcc
  条件: {a b : α}
  结论: (cIcc a b)ᶜ = cIoo b a
  证明: by
  ext
  rw [Set.mem_cIoo]; rw [sbtw_iff_not_btw]; rw [cIcc]; rw [mem_compl_iff]; rw [mem_ofPred]

Depends on / 依赖: Set.mem_cIoo, mem_cIoo, mem_compl_iff, mem_ofPred, sbtw_iff_not_btw
-/
theorem compl_cIcc {a b : α} : (cIcc a b)ᶜ = cIoo b a := by
  ext
  rw [Set.mem_cIoo]; rw [sbtw_iff_not_btw]; rw [cIcc]; rw [mem_compl_iff]; rw [mem_ofPred]

/--
theorem `compl_cIoo` / 定理 `compl_cIoo`

English:
theorem compl_cIoo
  given: {a b : α}
  statement: (cIoo a b)ᶜ = cIcc b a
  proof: by
  ext
  rw [Set.mem_cIcc]; rw [btw_iff_not_sbtw]; rw [cIoo]; rw [mem_compl_iff]; rw [mem_ofPred]

中文:
定理 compl_cIoo
  条件: {a b : α}
  结论: (cIoo a b)ᶜ = cIcc b a
  证明: by
  ext
  rw [Set.mem_cIcc]; rw [btw_iff_not_sbtw]; rw [cIoo]; rw [mem_compl_iff]; rw [mem_ofPred]

Depends on / 依赖: Set.mem_cIcc, btw_iff_not_sbtw, mem_cIcc, mem_compl_iff, mem_ofPred
-/
theorem compl_cIoo {a b : α} : (cIoo a b)ᶜ = cIcc b a := by
  ext
  rw [Set.mem_cIcc]; rw [btw_iff_not_sbtw]; rw [cIoo]; rw [mem_compl_iff]; rw [mem_ofPred]

end CircularOrder

end Set

/-! ### Circularizing instances -/


/--
Definition of `LE.toBtw` / `LE.toBtw` 的定义

English:
abbreviation LE.toBtw
  signature: (α : Type*) [LE α]
  body: a <= b ∧ b <= c ∨ b <= c ∧ c <= a ∨ c <= a ∧ a <= b

中文:
缩写 LE.toBtw
  签名: (α : 类型) [LE α]
  定义体: a <= b ∧ b <= c ∨ b <= c ∧ c <= a ∨ c <= a ∧ a <= b
-/
abbrev LE.toBtw (α : Type*) [LE α] : Btw α where
  btw a b c := a <= b ∧ b <= c ∨ b <= c ∧ c <= a ∨ c <= a ∧ a <= b

/--
Definition of `LT.toSBtw` / `LT.toSBtw` 的定义

English:
abbreviation LT.toSBtw
  signature: (α : Type*) [LT α]
  body: a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b

中文:
缩写 LT.toSBtw
  签名: (α : 类型) [LT α]
  定义体: a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b
-/
abbrev LT.toSBtw (α : Type*) [LT α] : SBtw α where
  sbtw a b c := a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b

section

variable {α : Type*} {a b c : α}

attribute [local instance] LE.toBtw LT.toSBtw

/--
lemma `btw_iff` / 引理 `btw_iff`

English:
lemma btw_iff
  given: [LE α]
  statement: btw a b c ↔ a <= b ∧ b <= c ∨ b <= c ∧ c <= a ∨ c <= a ∧ a <= b
  proof: .rfl

中文:
引理 btw_iff
  条件: [LE α]
  结论: btw a b c ↔ a <= b ∧ b <= c ∨ b <= c ∧ c <= a ∨ c <= a ∧ a <= b
  证明: .rfl
-/
lemma btw_iff [LE α] : btw a b c ↔ a <= b ∧ b <= c ∨ b <= c ∧ c <= a ∨ c <= a ∧ a <= b := .rfl
/--
lemma `sbtw_iff` / 引理 `sbtw_iff`

English:
lemma sbtw_iff
  given: [LT α]
  statement: sbtw a b c ↔ a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b
  proof: .rfl

中文:
引理 sbtw_iff
  条件: [LT α]
  结论: sbtw a b c ↔ a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b
  证明: .rfl
-/
lemma sbtw_iff [LT α] : sbtw a b c ↔ a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b := .rfl

end

/--
Definition of `Preorder.toCircularPreorder` / `Preorder.toCircularPreorder` 的定义

English:
abbreviation Preorder.toCircularPreorder
  signature: (α : Type*) [Preorder α]
  body: a <= b ∧ b <= c ∨ b <= c ∧ c <= a ∨ c <= a ∧ a <= b
  sbtw a b c := a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b
  btw_refl _ := .inl ⟨le_rfl, le_rfl⟩
  btw_cyclic_left {a b c} := .rotate
  sbtw_trans_left {a b c d} := by
    rintro (⟨hab, hbc⟩ | ⟨hbc, hca⟩ | ⟨hca, hab⟩) (⟨hbd, hdc⟩ | ⟨hdc, hcb⟩ | 

中文:
缩写 Preorder.toCircularPreorder
  签名: (α : 类型) [Preorder α]
  定义体: a <= b ∧ b <= c ∨ b <= c ∧ c <= a ∨ c <= a ∧ a <= b
  sbtw a b c := a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b
  btw_refl _ := .inl ⟨le_rfl, le_rfl⟩
  btw_cyclic_left {a b c} := .rotate
  sbtw_trans_left {a b c d} := by
    rintro (⟨hab, hbc⟩ | ⟨hbc, hca⟩ | ⟨hca, hab⟩) (⟨hbd, hdc⟩ | ⟨hdc, hcb⟩ | 
-/
abbrev Preorder.toCircularPreorder (α : Type*) [Preorder α] : CircularPreorder α where
  btw a b c := a <= b ∧ b <= c ∨ b <= c ∧ c <= a ∨ c <= a ∧ a <= b
  sbtw a b c := a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b
  btw_refl _ := .inl ⟨le_rfl, le_rfl⟩
  btw_cyclic_left {a b c} := .rotate
  sbtw_trans_left {a b c d} := by
    rintro (⟨hab, hbc⟩ | ⟨hbc, hca⟩ | ⟨hca, hab⟩) (⟨hbd, hdc⟩ | ⟨hdc, hcb⟩ | ⟨hcb, hbd⟩) <;>
      first
      | refine .inl ?_; constructor <;> order
| refine .inr .inl ?_; constructor <;> order
| refine .inr .inr ?_; constructor <;> order
  sbtw_iff_btw_not_btw {a b c} := by
    simp_rw [lt_iff_le_not_ge]
    grind

/--
Definition of `PartialOrder.toCircularPartialOrder` / `PartialOrder.toCircularPartialOrder` 的定义

English:
abbreviation PartialOrder.toCircularPartialOrder
  signature: (α : Type*) [PartialOrder α]
  body: { Preorder.toCircularPreorder α with
    btw_antisymm := fun {a b c} => by
      rintro (⟨hab, hbc⟩ | ⟨hbc, hca⟩ | ⟨hca, hab⟩) (⟨hcb, hba⟩ | ⟨hba, hac⟩ | ⟨hac, hcb⟩)
      · exact Or.inl (hab.antisymm hba)
      · exact Or.inl (hab.antisymm hba)
      · exact Or.inr (Or.inl <| hbc.antisymm hcb)
    

中文:
缩写 PartialOrder.toCircularPartialOrder
  签名: (α : 类型) [PartialOrder α]
  定义体: { Preorder.toCircularPreorder α with
    btw_antisymm := fun {a b c} => by
      rintro (⟨hab, hbc⟩ | ⟨hbc, hca⟩ | ⟨hca, hab⟩) (⟨hcb, hba⟩ | ⟨hba, hac⟩ | ⟨hac, hcb⟩)
      · exact Or.inl (hab.antisymm hba)
      · exact Or.inl (hab.antisymm hba)
      · exact Or.inr (Or.inl <| hbc.antisymm hcb)
    

Depends on / 依赖: Or.inl, Or.inr, Preorder, Preorder.toCircularPreorder, antisymm, btw_antisymm, hab.antisymm, hbc.antisymm, hca.an, hca.antisymm, toCircularPreorder
-/
abbrev PartialOrder.toCircularPartialOrder (α : Type*) [PartialOrder α] : CircularPartialOrder α :=
  { Preorder.toCircularPreorder α with
    btw_antisymm := fun {a b c} => by
      rintro (⟨hab, hbc⟩ | ⟨hbc, hca⟩ | ⟨hca, hab⟩) (⟨hcb, hba⟩ | ⟨hba, hac⟩ | ⟨hac, hcb⟩)
      · exact Or.inl (hab.antisymm hba)
      · exact Or.inl (hab.antisymm hba)
      · exact Or.inr (Or.inl <| hbc.antisymm hcb)
      · exact Or.inr (Or.inl <| hbc.antisymm hcb)
      · exact Or.inr (Or.inr <| hca.antisymm hac)
      · exact Or.inr (Or.inl <| hbc.antisymm hcb)
      · exact Or.inl (hab.antisymm hba)
      · exact Or.inl (hab.antisymm hba)
      · exact Or.inr (Or.inr <| hca.antisymm hac) }

/--
Definition of `LinearOrder.toCircularOrder` / `LinearOrder.toCircularOrder` 的定义

English:
abbreviation LinearOrder.toCircularOrder
  signature: (α : Type*) [LinearOrder α]
  body: { PartialOrder.toCircularPartialOrder α with
    btw_total := fun a b c => by
      rcases le_total a b with hab | hba <;> rcases le_total b c with hbc | hcb <;>
        rcases le_total c a with hca | hac
      · exact Or.inl (Or.inl ⟨hab, hbc⟩)
      · exact Or.inl (Or.inl ⟨hab, hbc⟩)
      · exact

中文:
缩写 LinearOrder.toCircularOrder
  签名: (α : 类型) [LinearOrder α]
  定义体: { PartialOrder.toCircularPartialOrder α with
    btw_total := fun a b c => by
      rcases le_total a b with hab | hba <;> rcases le_total b c with hbc | hcb <;>
        rcases le_total c a with hca | hac
      · exact Or.inl (Or.inl ⟨hab, hbc⟩)
      · exact Or.inl (Or.inl ⟨hab, hbc⟩)
      · exact

Depends on / 依赖: Or.inl, Or.inr, PartialOrder, PartialOrder.toCircularPartialOrder, btw_total, le_total, toCircularPartialOrder
-/
abbrev LinearOrder.toCircularOrder (α : Type*) [LinearOrder α] : CircularOrder α :=
  { PartialOrder.toCircularPartialOrder α with
    btw_total := fun a b c => by
      rcases le_total a b with hab | hba <;> rcases le_total b c with hbc | hcb <;>
        rcases le_total c a with hca | hac
      · exact Or.inl (Or.inl ⟨hab, hbc⟩)
      · exact Or.inl (Or.inl ⟨hab, hbc⟩)
      · exact Or.inl (Or.inr <| Or.inr ⟨hca, hab⟩)
      · exact Or.inr (Or.inr <| Or.inr ⟨hac, hcb⟩)
      · exact Or.inl (Or.inr <| Or.inl ⟨hbc, hca⟩)
      · exact Or.inr (Or.inr <| Or.inl ⟨hba, hac⟩)
      · exact Or.inr (Or.inl ⟨hcb, hba⟩)
      · exact Or.inr (Or.inr <| Or.inl ⟨hba, hac⟩) }

/-! ### Dual constructions -/


namespace OrderDual

/--
Instance `btw` / 实例 `btw`

English:
instance btw
  signature: (α : Type*) [h : Btw α]
  body: ⟨fun a b c => h.btw c b a⟩

中文:
实例 btw
  签名: (α : 类型) [h : Btw α]
  定义体: ⟨fun a b c => h.btw c b a⟩

Depends on / 依赖: h.btw
-/
instance btw (α : Type*) [h : Btw α] : Btw αᵒᵈ :=
  ⟨fun a b c => h.btw c b a⟩

/--
Instance `sbtw` / 实例 `sbtw`

English:
instance sbtw
  signature: (α : Type*) [h : SBtw α]
  body: ⟨fun a b c => h.sbtw c b a⟩

中文:
实例 sbtw
  签名: (α : 类型) [h : SBtw α]
  定义体: ⟨fun a b c => h.sbtw c b a⟩

Depends on / 依赖: h.sbtw
-/
instance sbtw (α : Type*) [h : SBtw α] : SBtw αᵒᵈ :=
  ⟨fun a b c => h.sbtw c b a⟩

/--
Instance `circularPreorder` / 实例 `circularPreorder`

English:
instance circularPreorder
  signature: (α : Type*) [CircularPreorder α]
  body: btw_refl _
  btw_cyclic_left {_ _ _} := @btw_cyclic_right α _ _ _ _
  sbtw_trans_left {_ _ _ _} habc hbdc := hbdc.trans_right habc
  sbtw_iff_btw_not_btw {a b c} := @sbtw_iff_btw_not_btw α _ c b a

中文:
实例 circularPreorder
  签名: (α : 类型) [CircularPreorder α]
  定义体: btw_refl _
  btw_cyclic_left {_ _ _} := @btw_cyclic_right α _ _ _ _
  sbtw_trans_left {_ _ _ _} habc hbdc := hbdc.trans_right habc
  sbtw_iff_btw_not_btw {a b c} := @sbtw_iff_btw_not_btw α _ c b a

Depends on / 依赖: btw_refl
-/
instance circularPreorder (α : Type*) [CircularPreorder α] : CircularPreorder αᵒᵈ where
  btw_refl _ := btw_refl _
  btw_cyclic_left {_ _ _} := @btw_cyclic_right α _ _ _ _
  sbtw_trans_left {_ _ _ _} habc hbdc := hbdc.trans_right habc
  sbtw_iff_btw_not_btw {a b c} := @sbtw_iff_btw_not_btw α _ c b a

/--
Instance `circularPartialOrder` / 实例 `circularPartialOrder`

English:
instance circularPartialOrder
  signature: (α : Type*) [CircularPartialOrder α]
  body: fun {_ _ _} habc hcba => @btw_antisymm α _ _ _ _ hcba habc

中文:
实例 circularPartialOrder
  签名: (α : 类型) [CircularPartialOrder α]
  定义体: fun {_ _ _} habc hcba => @btw_antisymm α _ _ _ _ hcba habc

Depends on / 依赖: btw_antisymm
-/
instance circularPartialOrder (α : Type*) [CircularPartialOrder α] : CircularPartialOrder αᵒᵈ where
  btw_antisymm := fun {_ _ _} habc hcba => @btw_antisymm α _ _ _ _ hcba habc

instance (α : Type*) [CircularOrder α] : CircularOrder αᵒᵈ where
  btw_total := fun {a b c} => @btw_total α _ c b a

end OrderDual
