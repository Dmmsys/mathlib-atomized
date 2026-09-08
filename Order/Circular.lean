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

/-- Syntax typeclass for a betweenness relation. -/
/-
**Btw** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Syntax typeclass for a betweenness relation.
-/
class Btw (α : Type*) where
  /-- Betweenness for circular orders. `btw a b c` states that `b` is between `a` and `c` (in that
  order). -/
  btw : α → α → α → Prop

export Btw (btw)

/-- Syntax typeclass for a strict betweenness relation. -/
/-
**SBtw** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Syntax typeclass for a strict betweenness relation.
-/
class SBtw (α : Type*) where
  /-- Strict betweenness for circular orders. `sbtw a b c` states that `b` is strictly between `a`
  and `c` (in that order). -/
  sbtw : α → α → α → Prop

export SBtw (sbtw)

/-- A circular preorder is the analogue of a preorder where you can loop around. `≤` and `<` are
replaced by ternary relations `btw` and `sbtw`. `btw` is reflexive and cyclic. `sbtw` is transitive.
-/
/-
**CircularPreorder** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：CircularPreorder (α : Type*) extends Btw α, SBtw α where /-- `a` is betwee
n `a` and `a`. -/ btw_refl (a : α) : btw a a a /-- If `b` is between `a` and `c`
, then `c` is between `b` and `a`. This is motivated by imagining three points o
n a circle. -/ btw_cyclic_left {a b c : α} : btw a b c -> btw b c a sbtw
参数：α : Type*；a : α。
继承自：Btw α, SBtw α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A circular preorder is the analogue of a preorder where you can loop around. `≤`
 and `<` are
replaced by ternary relations `btw` and `sbtw`. `btw` is reflexive and cyclic. `
sbtw` is transitive.
-/
class CircularPreorder (α : Type*) extends Btw α, SBtw α where
  /-- `a` is between `a` and `a`. -/
  btw_refl (a : α) : btw a a a
  /-- If `b` is between `a` and `c`, then `c` is between `b` and `a`.
  This is motivated by imagining three points on a circle. -/
  btw_cyclic_left {a b c : α} : btw a b c → btw b c a
  sbtw := fun a b c => btw a b c ∧ ¬btw c b a
  /-- Strict betweenness is given by betweenness in one direction and non-betweenness in the other.

  I.e., if `b` is between `a` and `c` but not between `c` and `a`, then we say `b` is strictly
  between `a` and `c`. -/
  sbtw_iff_btw_not_btw {a b c : α} : sbtw a b c ↔ btw a b c ∧ ¬btw c b a := by intros; rfl
  /-- For any fixed `c`, `fun a b ↦ sbtw a b c` is a transitive relation.

  I.e., given `a` `b` `d` `c` in that "order", if we have `b` strictly between `a` and `c`, and `d`
  strictly between `b` and `c`, then `d` is strictly between `a` and `c`. -/
  sbtw_trans_left {a b c d : α} : sbtw a b c → sbtw b d c → sbtw a d c

export CircularPreorder (btw_refl btw_cyclic_left sbtw_trans_left)

/-- A circular partial order is the analogue of a partial order where you can loop around. `≤` and
`<` are replaced by ternary relations `btw` and `sbtw`. `btw` is reflexive, cyclic and
antisymmetric. `sbtw` is transitive. -/
/-
**CircularPartialOrder** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A circular partial order is the analogue of a partial order where you can loop a
round. `≤` and
`<` are replaced by ternary relations `btw` and `sbtw`. `btw` is reflexive, cycl
ic and
antisymmetric. `sbtw` is transitive.
-/
class CircularPartialOrder (α : Type*) extends CircularPreorder α where
  /-- If `b` is between `a` and `c` and also between `c` and `a`, then at least one pair of points
  among `a`, `b`, `c` are identical. -/
  btw_antisymm {a b c : α} : btw a b c → btw c b a → a = b ∨ b = c ∨ c = a

export CircularPartialOrder (btw_antisymm)

/-- A circular order is the analogue of a linear order where you can loop around. `≤` and `<` are
replaced by ternary relations `btw` and `sbtw`. `btw` is reflexive, cyclic, antisymmetric and total.
`sbtw` is transitive. -/
/-
**CircularOrder** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A circular order is the analogue of a linear order where you can loop around. `≤
` and `<` are
replaced by ternary relations `btw` and `sbtw`. `btw` is reflexive, cyclic, anti
symmetric and total.
`sbtw` is transitive.
-/
class CircularOrder (α : Type*) extends CircularPartialOrder α where
  /-- For any triple of points, the second is between the other two one way or another. -/
  btw_total : ∀ a b c : α, btw a b c ∨ btw c b a

export CircularOrder (btw_total)

/-! ### Circular preorders -/


section CircularPreorder

variable {α : Type*} [CircularPreorder α]

/-
**btw_rfl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：btw_rfl {a : α} : btw a a a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircularPreorder.btw_refl`：∀ {α : Type u_1} [self : CircularPreorder α] 
(a : α), btw a a a
-/
theorem btw_rfl {a : α} : btw a a a :=
  btw_refl _

-- TODO: `alias` creates a def instead of a lemma (because `btw_cyclic_left` is a def).
-- alias btw_cyclic_left        ← Btw.btw.cyclic_left
/-
**Btw.btw.cyclic_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Btw.btw.cyclic_left {a b c : α} (h : btw a b c) : btw b c a
参数：h : btw a b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircularPreorder.btw_cyclic_left`：∀ {α : Type u_1} [self : CircularPreor
der α] {a b c : α}, btw a b c → btw b c a
-/
theorem Btw.btw.cyclic_left {a b c : α} (h : btw a b c) : btw b c a :=
  btw_cyclic_left h
/-
**btw_cyclic_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：btw_cyclic_right {a b c : α} (h : btw a b c) : btw c a b
参数：h : btw a b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Btw.btw.cyclic_left`：Btw.btw.cyclic_left {a b c : α} (h : btw a b c) : b
tw b c a
-/
theorem btw_cyclic_right {a b c : α} (h : btw a b c) : btw c a b :=
  h.cyclic_left.cyclic_left

alias Btw.btw.cyclic_right := btw_cyclic_right

/-- The order of the `↔` has been chosen so that `rw [btw_cyclic]` cycles to the right while
`rw [← btw_cyclic]` cycles to the left (thus following the prepended arrow). -/
/-
**btw_cyclic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：btw_cyclic {a b c : α} : btw a b c ↔ btw c a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `btw_cyclic_right`：btw_cyclic_right {a b c : α} (h : btw a b c) : btw c a
 b
· 使用定理 `CircularPreorder.btw_cyclic_left`：∀ {α : Type u_1} [self : CircularPreor
der α] {a b c : α}, btw a b c → btw b c a

--- 原说明 ---
The order of the `↔` has been chosen so that `rw [btw_cyclic]` cycles to the rig
ht while
`rw [← btw_cyclic]` cycles to the left (thus following the prepended arrow).
-/
theorem btw_cyclic {a b c : α} : btw a b c ↔ btw c a b :=
  ⟨btw_cyclic_right, btw_cyclic_left⟩
/-
**sbtw_iff_btw_not_btw** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_iff_btw_not_btw {a b c : α} : sbtw a b c ↔ btw a b c ∧ ¬btw c b a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircularPreorder.sbtw_iff_btw_not_btw`：∀ {α : Type u_1} [self : Circular
Preorder α] {a b c : α}, sbtw a b c ↔ btw a b c ∧ ¬btw c b a
-/
theorem sbtw_iff_btw_not_btw {a b c : α} : sbtw a b c ↔ btw a b c ∧ ¬btw c b a :=
  CircularPreorder.sbtw_iff_btw_not_btw
/-
**btw_of_sbtw** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：btw_of_sbtw {a b c : α} (h : sbtw a b c) : btw a b c
参数：h : sbtw a b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sbtw_iff_btw_not_btw`：sbtw_iff_btw_not_btw {a b c : α} : sbtw a b c ↔ bt
w a b c ∧ ¬btw c b a
-/
theorem btw_of_sbtw {a b c : α} (h : sbtw a b c) : btw a b c :=
  (sbtw_iff_btw_not_btw.1 h).1

alias SBtw.sbtw.btw := btw_of_sbtw
/-
**not_btw_of_sbtw** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_btw_of_sbtw {a b c : α} (h : sbtw a b c) : ¬btw c b a
参数：h : sbtw a b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sbtw_iff_btw_not_btw`：sbtw_iff_btw_not_btw {a b c : α} : sbtw a b c ↔ bt
w a b c ∧ ¬btw c b a
-/
theorem not_btw_of_sbtw {a b c : α} (h : sbtw a b c) : ¬btw c b a :=
  (sbtw_iff_btw_not_btw.1 h).2

alias SBtw.sbtw.not_btw := not_btw_of_sbtw
/-
**not_sbtw_of_btw** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_sbtw_of_btw {a b c : α} (h : btw a b c) : ¬sbtw c b a
参数：h : btw a b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SBtw.sbtw.not_btw`：∀ {α : Type u_1} [inst : CircularPreorder α] {a b c :
 α}, sbtw a b c → ¬btw c b a
-/
theorem not_sbtw_of_btw {a b c : α} (h : btw a b c) : ¬sbtw c b a := fun h' => h'.not_btw h

alias Btw.btw.not_sbtw := not_sbtw_of_btw
/-
**sbtw_of_btw_not_btw** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_of_btw_not_btw {a b c : α} (habc : btw a b c) (hcba : ¬btw c b a) : s
btw a b c
参数：habc : btw a b c；hcba : ¬btw c b a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sbtw_iff_btw_not_btw`：sbtw_iff_btw_not_btw {a b c : α} : sbtw a b c ↔ bt
w a b c ∧ ¬btw c b a
-/
theorem sbtw_of_btw_not_btw {a b c : α} (habc : btw a b c) (hcba : ¬btw c b a) : sbtw a b c :=
  sbtw_iff_btw_not_btw.2 ⟨habc, hcba⟩

alias Btw.btw.sbtw_of_not_btw := sbtw_of_btw_not_btw
/-
**sbtw_cyclic_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_cyclic_left {a b c : α} (h : sbtw a b c) : sbtw b c a
参数：h : sbtw a b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Btw.btw.sbtw_of_not_btw`：∀ {α : Type u_1} [inst : CircularPreorder α] {a
 b c : α}, btw a b c → ¬btw c b a → sbtw a b c
· 使用定理 `Btw.btw.cyclic_left`：Btw.btw.cyclic_left {a b c : α} (h : btw a b c) : b
tw b c a
· 使用定理 `SBtw.sbtw.btw`：∀ {α : Type u_1} [inst : CircularPreorder α] {a b c : α},
 sbtw a b c → btw a b c
· 使用定理 `SBtw.sbtw.not_btw`：∀ {α : Type u_1} [inst : CircularPreorder α] {a b c :
 α}, sbtw a b c → ¬btw c b a
-/
theorem sbtw_cyclic_left {a b c : α} (h : sbtw a b c) : sbtw b c a :=
  h.btw.cyclic_left.sbtw_of_not_btw fun h' => h.not_btw h'.cyclic_left

alias SBtw.sbtw.cyclic_left := sbtw_cyclic_left
/-
**sbtw_cyclic_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_cyclic_right {a b c : α} (h : sbtw a b c) : sbtw c a b
参数：h : sbtw a b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SBtw.sbtw.cyclic_left`：∀ {α : Type u_1} [inst : CircularPreorder α] {a b
 c : α}, sbtw a b c → sbtw b c a
-/
theorem sbtw_cyclic_right {a b c : α} (h : sbtw a b c) : sbtw c a b :=
  h.cyclic_left.cyclic_left

alias SBtw.sbtw.cyclic_right := sbtw_cyclic_right

/-- The order of the `↔` has been chosen so that `rw [sbtw_cyclic]` cycles to the right while
`rw [← sbtw_cyclic]` cycles to the left (thus following the prepended arrow). -/
/-
**sbtw_cyclic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_cyclic {a b c : α} : sbtw a b c ↔ sbtw c a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sbtw_cyclic_right`：sbtw_cyclic_right {a b c : α} (h : sbtw a b c) : sbtw
 c a b
· 使用定理 `sbtw_cyclic_left`：sbtw_cyclic_left {a b c : α} (h : sbtw a b c) : sbtw b
 c a

--- 原说明 ---
The order of the `↔` has been chosen so that `rw [sbtw_cyclic]` cycles to the ri
ght while
`rw [← sbtw_cyclic]` cycles to the left (thus following the prepended arrow).
-/
theorem sbtw_cyclic {a b c : α} : sbtw a b c ↔ sbtw c a b :=
  ⟨sbtw_cyclic_right, sbtw_cyclic_left⟩

-- TODO: `alias` creates a def instead of a lemma (because `sbtw_trans_left` is a def).
-- alias btw_trans_left        ← SBtw.sbtw.trans_left
/-
**SBtw.sbtw.trans_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SBtw.sbtw.trans_left {a b c d : α} (h : sbtw a b c) : sbtw b d c -> sbtw a
 d c
参数：h : sbtw a b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircularPreorder.sbtw_trans_left`：∀ {α : Type u_1} [self : CircularPreor
der α] {a b c d : α}, sbtw a b c → sbtw b d c → sbtw a d c
-/
theorem SBtw.sbtw.trans_left {a b c d : α} (h : sbtw a b c) : sbtw b d c → sbtw a d c :=
  sbtw_trans_left h
/-
**sbtw_trans_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_trans_right {a b c d : α} (hbc : sbtw a b c) (hcd : sbtw a c d) : sbt
w a b d
参数：hbc : sbtw a b c；hcd : sbtw a c d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SBtw.sbtw.cyclic_right`：∀ {α : Type u_1} [inst : CircularPreorder α] {a 
b c : α}, sbtw a b c → sbtw c a b
· 使用定理 `SBtw.sbtw.trans_left`：SBtw.sbtw.trans_left {a b c d : α} (h : sbtw a b c
) : sbtw b d c -> sbtw a d c
· 使用定理 `SBtw.sbtw.cyclic_left`：∀ {α : Type u_1} [inst : CircularPreorder α] {a b
 c : α}, sbtw a b c → sbtw b c a
-/
theorem sbtw_trans_right {a b c d : α} (hbc : sbtw a b c) (hcd : sbtw a c d) : sbtw a b d :=
  (hbc.cyclic_left.trans_left hcd.cyclic_left).cyclic_right

alias SBtw.sbtw.trans_right := sbtw_trans_right
/-
**sbtw_asymm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_asymm {a b c : α} (h : sbtw a b c) : ¬sbtw c b a
参数：h : sbtw a b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Btw.btw.not_sbtw`：∀ {α : Type u_1} [inst : CircularPreorder α] {a b c : 
α}, btw a b c → ¬sbtw c b a
· 使用定理 `SBtw.sbtw.btw`：∀ {α : Type u_1} [inst : CircularPreorder α] {a b c : α},
 sbtw a b c → btw a b c
-/
theorem sbtw_asymm {a b c : α} (h : sbtw a b c) : ¬sbtw c b a :=
  h.btw.not_sbtw

alias SBtw.sbtw.not_sbtw := sbtw_asymm
/-
**sbtw_irrefl_left_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_irrefl_left_right {a b : α} : ¬sbtw a b a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SBtw.sbtw.not_btw`：∀ {α : Type u_1} [inst : CircularPreorder α] {a b c :
 α}, sbtw a b c → ¬btw c b a
· 使用定理 `SBtw.sbtw.btw`：∀ {α : Type u_1} [inst : CircularPreorder α] {a b c : α},
 sbtw a b c → btw a b c
-/
theorem sbtw_irrefl_left_right {a b : α} : ¬sbtw a b a := fun h => h.not_btw h.btw
/-
**sbtw_irrefl_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_irrefl_left {a b : α} : ¬sbtw a a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sbtw_irrefl_left_right`：sbtw_irrefl_left_right {a b : α} : ¬sbtw a b a
· 使用定理 `SBtw.sbtw.cyclic_left`：∀ {α : Type u_1} [inst : CircularPreorder α] {a b
 c : α}, sbtw a b c → sbtw b c a
-/
theorem sbtw_irrefl_left {a b : α} : ¬sbtw a a b := fun h => sbtw_irrefl_left_right h.cyclic_left
/-
**sbtw_irrefl_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_irrefl_right {a b : α} : ¬sbtw a b b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sbtw_irrefl_left_right`：sbtw_irrefl_left_right {a b : α} : ¬sbtw a b a
· 使用定理 `SBtw.sbtw.cyclic_right`：∀ {α : Type u_1} [inst : CircularPreorder α] {a 
b c : α}, sbtw a b c → sbtw c a b
-/
theorem sbtw_irrefl_right {a b : α} : ¬sbtw a b b := fun h => sbtw_irrefl_left_right h.cyclic_right
/-
**sbtw_irrefl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_irrefl (a : α) : ¬sbtw a a a
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sbtw_irrefl_left_right`：sbtw_irrefl_left_right {a b : α} : ¬sbtw a b a
-/
theorem sbtw_irrefl (a : α) : ¬sbtw a a a :=
  sbtw_irrefl_left_right

end CircularPreorder

/-! ### Circular partial orders -/


section CircularPartialOrder

variable {α : Type*} [CircularPartialOrder α]

-- TODO: `alias` creates a def instead of a lemma (because `btw_antisymm` is a def).
-- alias btw_antisymm        ← Btw.btw.antisymm
/-
**Btw.btw.antisymm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Btw.btw.antisymm {a b c : α} (h : btw a b c) : btw c b a -> a = b ∨ b = c 
∨ c = a
参数：h : btw a b c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircularPartialOrder.btw_antisymm`：∀ {α : Type u_1} [self : CircularPart
ialOrder α] {a b c : α}, btw a b c → btw c b a → a = b ∨ b = c ∨ c = a
-/
theorem Btw.btw.antisymm {a b c : α} (h : btw a b c) : btw c b a → a = b ∨ b = c ∨ c = a :=
  btw_antisymm h

end CircularPartialOrder

/-! ### Circular orders -/


section CircularOrder

variable {α : Type*} [CircularOrder α]

/-
**btw_refl_left_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：btw_refl_left_right (a b : α) : btw a b a
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `or_self_iff`：∀ {a : Prop}, a ∨ a ↔ a
· 使用定理 `CircularOrder.btw_total`：∀ {α : Type u_1} [self : CircularOrder α] (a b 
c : α), btw a b c ∨ btw c b a
-/
theorem btw_refl_left_right (a b : α) : btw a b a :=
  or_self_iff.1 (btw_total a b a)
/-
**btw_rfl_left_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：btw_rfl_left_right {a b : α} : btw a b a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `btw_refl_left_right`：btw_refl_left_right (a b : α) : btw a b a
-/
theorem btw_rfl_left_right {a b : α} : btw a b a :=
  btw_refl_left_right _ _
/-
**btw_refl_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：btw_refl_left (a b : α) : btw a a b
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Btw.btw.cyclic_right`：∀ {α : Type u_1} [inst : CircularPreorder α] {a b 
c : α}, btw a b c → btw c a b
· 使用定理 `btw_rfl_left_right`：btw_rfl_left_right {a b : α} : btw a b a
-/
theorem btw_refl_left (a b : α) : btw a a b :=
  btw_rfl_left_right.cyclic_right
/-
**btw_rfl_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：btw_rfl_left {a b : α} : btw a a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `btw_refl_left`：btw_refl_left (a b : α) : btw a a b
-/
theorem btw_rfl_left {a b : α} : btw a a b :=
  btw_refl_left _ _
/-
**btw_refl_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：btw_refl_right (a b : α) : btw a b b
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Btw.btw.cyclic_left`：Btw.btw.cyclic_left {a b c : α} (h : btw a b c) : b
tw b c a
· 使用定理 `btw_rfl_left_right`：btw_rfl_left_right {a b : α} : btw a b a
-/
theorem btw_refl_right (a b : α) : btw a b b :=
  btw_rfl_left_right.cyclic_left
/-
**btw_rfl_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：btw_rfl_right {a b : α} : btw a b b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `btw_refl_right`：btw_refl_right (a b : α) : btw a b b
-/
theorem btw_rfl_right {a b : α} : btw a b b :=
  btw_refl_right _ _
/-
**sbtw_iff_not_btw** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sbtw_iff_not_btw {a b c : α} : sbtw a b c ↔ ¬btw c b a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sbtw_iff_btw_not_btw`：sbtw_iff_btw_not_btw {a b c : α} : sbtw a b c ↔ bt
w a b c ∧ ¬btw c b a
· 使用定理 `and_iff_right_of_imp`：∀ {b a : Prop}, (b → a) → (a ∧ b ↔ b)
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `CircularOrder.btw_total`：∀ {α : Type u_1} [self : CircularOrder α] (a b 
c : α), btw a b c ∨ btw c b a
-/
theorem sbtw_iff_not_btw {a b c : α} : sbtw a b c ↔ ¬btw c b a := by
  rw [sbtw_iff_btw_not_btw]
  exact and_iff_right_of_imp (btw_total _ _ _).resolve_left
/-
**btw_iff_not_sbtw** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：btw_iff_not_sbtw {a b c : α} : btw a b c ↔ ¬sbtw c b a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `iff_not_comm`：iff_not_comm : (a ↔ ¬b) ↔ (b ↔ ¬a)
· 使用定理 `sbtw_iff_not_btw`：sbtw_iff_not_btw {a b c : α} : sbtw a b c ↔ ¬btw c b a
-/
theorem btw_iff_not_sbtw {a b c : α} : btw a b c ↔ ¬sbtw c b a :=
  iff_not_comm.1 sbtw_iff_not_btw

end CircularOrder

/-! ### Circular intervals -/


namespace Set

section CircularPreorder

variable {α : Type*} [CircularPreorder α]

/-- Closed-closed circular interval -/
/-
**Set.cIcc** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：cIcc (a b : α) : Set α
参数：a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Closed-closed circular interval
-/
def cIcc (a b : α) : Set α :=
  { x | btw a x b }

/-- Open-open circular interval -/
/-
**Set.cIoo** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：cIoo (a b : α) : Set α
参数：a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Open-open circular interval
-/
def cIoo (a b : α) : Set α :=
  { x | sbtw a x b }

@[simp]
/-
**Set.mem_cIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_cIcc {a b x : α} : x in cIcc a b ↔ btw a x b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_cIcc {a b x : α} : x ∈ cIcc a b ↔ btw a x b :=
  Iff.rfl

@[simp]
/-
**Set.mem_cIoo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_cIoo {a b x : α} : x in cIoo a b ↔ sbtw a x b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_cIoo {a b x : α} : x ∈ cIoo a b ↔ sbtw a x b :=
  Iff.rfl

end CircularPreorder

section CircularOrder

variable {α : Type*} [CircularOrder α]

/-
**Set.left_mem_cIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：left_mem_cIcc (a b : α) : a in cIcc a b
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `btw_rfl_left`：btw_rfl_left {a b : α} : btw a a b
-/
theorem left_mem_cIcc (a b : α) : a ∈ cIcc a b :=
  btw_rfl_left
/-
**Set.right_mem_cIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：right_mem_cIcc (a b : α) : b in cIcc a b
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `btw_rfl_right`：btw_rfl_right {a b : α} : btw a b b
-/
theorem right_mem_cIcc (a b : α) : b ∈ cIcc a b :=
  btw_rfl_right
/-
**Set.compl_cIcc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_cIcc {a b : α} : (cIcc a b)ᶜ = cIoo b a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_cIoo`：mem_cIoo {a b x : α} : x in cIoo a b ↔ sbtw a x b
· 使用定理 `sbtw_iff_not_btw`：sbtw_iff_not_btw {a b c : α} : sbtw a b c ↔ ¬btw c b a
· 使用定理 `Set.cIcc.eq_1`：∀ {α : Type u_1} [inst : CircularPreorder α] (a b : α), S
et.cIcc a b = {x | btw a x b}
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem compl_cIcc {a b : α} : (cIcc a b)ᶜ = cIoo b a := by
  ext
  rw [Set.mem_cIoo, sbtw_iff_not_btw, cIcc, mem_compl_iff, mem_ofPred]
/-
**Set.compl_cIoo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_cIoo {a b : α} : (cIoo a b)ᶜ = cIcc b a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_cIcc`：mem_cIcc {a b x : α} : x in cIcc a b ↔ btw a x b
· 使用定理 `btw_iff_not_sbtw`：btw_iff_not_sbtw {a b c : α} : btw a b c ↔ ¬sbtw c b a
· 使用定理 `Set.cIoo.eq_1`：∀ {α : Type u_1} [inst : CircularPreorder α] (a b : α), S
et.cIoo a b = {x | sbtw a x b}
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem compl_cIoo {a b : α} : (cIoo a b)ᶜ = cIcc b a := by
  ext
  rw [Set.mem_cIcc, btw_iff_not_sbtw, cIoo, mem_compl_iff, mem_ofPred]

end CircularOrder

end Set

/-! ### Circularizing instances -/


/-- The betweenness relation obtained from "looping around" `≤`.
See note [reducible non-instances]. -/
/-
**LE.toBtw** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LE.toBtw (α : Type*) [LE α] : Btw α where btw a b c
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The betweenness relation obtained from "looping around" `≤`.
See note [reducible non-instances].
-/
abbrev LE.toBtw (α : Type*) [LE α] : Btw α where
  btw a b c := a ≤ b ∧ b ≤ c ∨ b ≤ c ∧ c ≤ a ∨ c ≤ a ∧ a ≤ b

/-- The strict betweenness relation obtained from "looping around" `<`.
See note [reducible non-instances]. -/
/-
**LT.toSBtw** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LT.toSBtw (α : Type*) [LT α] : SBtw α where sbtw a b c
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The strict betweenness relation obtained from "looping around" `<`.
See note [reducible non-instances].
-/
abbrev LT.toSBtw (α : Type*) [LT α] : SBtw α where
  sbtw a b c := a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b

section

variable {α : Type*} {a b c : α}

attribute [local instance] LE.toBtw LT.toSBtw

/-- The following lemmas are about the non-instances `LE.toBtw`, `LT.toSBtw` and
`LinearOrder.toCircularOrder`. -/
/-
**btw_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：btw_iff [LE α] : btw a b c ↔ a <= b ∧ b <= c ∨ b <= c ∧ c <= a ∨ c <= a ∧ 
a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The following lemmas are about the non-instances `LE.toBtw`, `LT.toSBtw` and
`LinearOrder.toCircularOrder`.
-/
lemma btw_iff [LE α] : btw a b c ↔ a ≤ b ∧ b ≤ c ∨ b ≤ c ∧ c ≤ a ∨ c ≤ a ∧ a ≤ b := .rfl
/-- The following lemmas are about the non-instances `LE.toBtw`, `LT.toSBtw` and
`LinearOrder.toCircularOrder`. -/
/-
**sbtw_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sbtw_iff [LT α] : sbtw a b c ↔ a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a <
 b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The following lemmas are about the non-instances `LE.toBtw`, `LT.toSBtw` and
`LinearOrder.toCircularOrder`.
-/
lemma sbtw_iff [LT α] : sbtw a b c ↔ a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b := .rfl

end

/-- The circular preorder obtained from "looping around" a preorder.
See note [reducible non-instances]. -/
/-
**Preorder.toCircularPreorder** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Preorder.toCircularPreorder (α : Type*) [Preorder α] : CircularPreorder α 
where btw a b c
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The circular preorder obtained from "looping around" a preorder.
See note [reducible non-instances].
-/
abbrev Preorder.toCircularPreorder (α : Type*) [Preorder α] : CircularPreorder α where
  btw a b c := a ≤ b ∧ b ≤ c ∨ b ≤ c ∧ c ≤ a ∨ c ≤ a ∧ a ≤ b
  sbtw a b c := a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b
  btw_refl _ := .inl ⟨le_rfl, le_rfl⟩
  btw_cyclic_left {a b c} := .rotate
  sbtw_trans_left {a b c d} := by
    rintro (⟨hab, hbc⟩ | ⟨hbc, hca⟩ | ⟨hca, hab⟩) (⟨hbd, hdc⟩ | ⟨hdc, hcb⟩ | ⟨hcb, hbd⟩) <;>
      first
      | refine .inl ?_; constructor <;> order
      | refine .inr <| .inl ?_; constructor <;> order
      | refine .inr <| .inr ?_; constructor <;> order
  sbtw_iff_btw_not_btw {a b c} := by
    simp_rw [lt_iff_le_not_ge]
    grind

/-- The circular partial order obtained from "looping around" a partial order.
See note [reducible non-instances]. -/
/-
**PartialOrder.toCircularPartialOrder** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：PartialOrder.toCircularPartialOrder (α : Type*) [PartialOrder α] : Circula
rPartialOrder α
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The circular partial order obtained from "looping around" a partial order.
See note [reducible non-instances].
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

/-- The circular order obtained from "looping around" a linear order.
See note [reducible non-instances]. -/
/-
**LinearOrder.toCircularOrder** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LinearOrder.toCircularOrder (α : Type*) [LinearOrder α] : CircularOrder α
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The circular order obtained from "looping around" a linear order.
See note [reducible non-instances].
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

/-
**OrderDual.btw** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
形式化陈述：btw (α : Type*) [h : Btw α] : Btw αᵒᵈ
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance btw (α : Type*) [h : Btw α] : Btw αᵒᵈ :=
  ⟨fun a b c => h.btw c b a⟩
/-
**OrderDual.sbtw** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
形式化陈述：sbtw (α : Type*) [h : SBtw α] : SBtw αᵒᵈ
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance sbtw (α : Type*) [h : SBtw α] : SBtw αᵒᵈ :=
  ⟨fun a b c => h.sbtw c b a⟩
/-
**OrderDual.circularPreorder** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
形式化陈述：circularPreorder (α : Type*) [CircularPreorder α] : CircularPreorder αᵒᵈ w
here btw_refl _
参数：α : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CircularPreorder.btw_refl`：∀ {α : Type u_1} [self : CircularPreorder α] 
(a : α), btw a a a
· 使用定理 `btw_cyclic_right`：btw_cyclic_right {a b c : α} (h : btw a b c) : btw c a
 b
· 使用定理 `sbtw_iff_btw_not_btw`：sbtw_iff_btw_not_btw {a b c : α} : sbtw a b c ↔ bt
w a b c ∧ ¬btw c b a
· 使用定理 `SBtw.sbtw.trans_right`：∀ {α : Type u_1} [inst : CircularPreorder α] {a b
 c d : α}, sbtw a b c → sbtw a c d → sbtw a b d
-/
instance circularPreorder (α : Type*) [CircularPreorder α] : CircularPreorder αᵒᵈ where
  btw_refl _ := btw_refl _
  btw_cyclic_left {_ _ _} := @btw_cyclic_right α _ _ _ _
  sbtw_trans_left {_ _ _ _} habc hbdc := hbdc.trans_right habc
  sbtw_iff_btw_not_btw {a b c} := @sbtw_iff_btw_not_btw α _ c b a
/-
**OrderDual.circularPartialOrder** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
形式化陈述：circularPartialOrder (α : Type*) [CircularPartialOrder α] : CircularPartia
lOrder αᵒᵈ where btw_antisymm
参数：α : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CircularPartialOrder.btw_antisymm`：∀ {α : Type u_1} [self : CircularPart
ialOrder α] {a b c : α}, btw a b c → btw c b a → a = b ∨ b = c ∨ c = a
-/
instance circularPartialOrder (α : Type*) [CircularPartialOrder α] : CircularPartialOrder αᵒᵈ where
  btw_antisymm := fun {_ _ _} habc hcba => @btw_antisymm α _ _ _ _ hcba habc
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [CircularOrder α] : CircularOrder αᵒᵈ where
  btw_total := fun {a b c} => @btw_total α _ c b a

end OrderDual

