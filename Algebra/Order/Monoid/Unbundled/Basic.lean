/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl, Damiano Testa,
Yuyang Zhao
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Data.Ordering.Basic
public import Mathlib.Order.MinMax
public import Mathlib.Tactic.Contrapose
public import Mathlib.Tactic.Use
public import Mathlib.Tactic.GRewrite

/-!
# Ordered monoids

This file develops the basics of ordered monoids.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.

## Remark

Almost no monoid is actually present in this file: most assumptions have been generalized to
`Mul` or `MulOneClass`.

-/

@[expose] public section


-- TODO: If possible, uniformize lemma names, taking special care of `'`,
-- after the `ordered`-refactor is done.
open Function

section Nat

/--
Instance `Nat.instMulLeftMono` / 实例 `Nat.instMulLeftMono`

English:
instance Nat.instMulLeftMono
  signature: : MulLeftMono Nat where
  body: fun _ _ _ h => mul_le_mul_left _ h

中文:
实例 自然数.instMulLeftMono
  签名: : MulLeftMono 自然数 where
  定义体: fun _ _ _ h => mul_le_mul_left _ h

Depends on / 依赖: mul_le_mul_left
-/
instance Nat.instMulLeftMono : MulLeftMono Nat where
  elim := fun _ _ _ h => mul_le_mul_left _ h

end Nat

section Int

/--
Instance `Int.instAddLeftMono` / 实例 `Int.instAddLeftMono`

English:
instance Int.instAddLeftMono
  signature: : AddLeftMono Int where
  body: fun _ _ _ h => Int.add_le_add_left h _

中文:
实例 整数.instAddLeftMono
  签名: : AddLeftMono 整数 where
  定义体: fun _ _ _ h => Int.add_le_add_left h _

Depends on / 依赖: Int.add_le_add_left, add_le_add_left
-/
instance Int.instAddLeftMono : AddLeftMono Int where
  elim := fun _ _ _ h => Int.add_le_add_left h _

end Int

variable {α β : Type*}

section Mul

variable [Mul α]

section LE

variable [LE α]

-- Note: in this section, we use `@[gcongr high]` so that these lemmas have a higher priority than
-- lemmas like `mul_le_mul_of_nonneg_left`, which have an extra side condition.

@[to_additive (attr := gcongr high - 1, to_dual self)]
/--
theorem `mul_le_mul_right` / 定理 `mul_le_mul_right`

English:
theorem mul_le_mul_right
  given: [MulLeftMono α] {b c : α} (bc : b <= c) (a : α)
  statement: a * b <= a * c
  proof: CovariantClass.elim _ bc

@[to_additive (attr := to_dual self) le_of_add_le_add_left]

中文:
定理 mul_le_mul_right
  条件: [MulLeftMono α] {b c : α} (bc : b <= c) (a : α)
  结论: a * b <= a * c
  证明: CovariantClass.elim _ bc

@[to_additive (attr := to_dual self) le_of_add_le_add_left]

Depends on / 依赖: CovariantClass, CovariantClass.elim
-/
theorem mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= c) (a : α) : a * b <= a * c :=
  CovariantClass.elim _ bc

@[to_additive (attr := to_dual self) le_of_add_le_add_left]
/--
theorem `le_of_mul_le_mul_left'` / 定理 `le_of_mul_le_mul_left'`

English:
theorem le_of_mul_le_mul_left'
  given: [MulLeftReflectLE α] {a b c : α} (bc : a * b <= a * c)
  statement: b <= c
  proof: MulLeftReflectLE.le_of_mul_le_mul_left' bc

@[to_additive (attr := gcongr high - 1, to_dual self)]

中文:
定理 le_of_mul_le_mul_left'
  条件: [MulLeftReflectLE α] {a b c : α} (bc : a * b <= a * c)
  结论: b <= c
  证明: MulLeftReflectLE.le_of_mul_le_mul_left' bc

@[to_additive (attr := gcongr high - 1, to_dual self)]

Depends on / 依赖: MulLeftReflectLE, MulLeftReflectLE.le_of_mul_le_mul_left, le_of_mul_le_mul_left
-/
theorem le_of_mul_le_mul_left' [MulLeftReflectLE α] {a b c : α} (bc : a * b <= a * c) : b <= c :=
  MulLeftReflectLE.le_of_mul_le_mul_left' bc

@[to_additive (attr := gcongr high - 1, to_dual self)]
/--
theorem `mul_le_mul_left` / 定理 `mul_le_mul_left`

English:
theorem mul_le_mul_left
  given: [i : MulRightMono α] {b c : α} (bc : b <= c) (a : α)
  statement: b * a <= c * a
  proof: i.elim a bc

@[to_additive (attr := to_dual self) le_of_add_le_add_right]

中文:
定理 mul_le_mul_left
  条件: [i : MulRightMono α] {b c : α} (bc : b <= c) (a : α)
  结论: b * a <= c * a
  证明: i.elim a bc

@[to_additive (attr := to_dual self) le_of_add_le_add_right]

Depends on / 依赖: i.elim
-/
theorem mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b <= c) (a : α) : b * a <= c * a :=
  i.elim a bc

@[to_additive (attr := to_dual self) le_of_add_le_add_right]
/--
theorem `le_of_mul_le_mul_right'` / 定理 `le_of_mul_le_mul_right'`

English:
theorem le_of_mul_le_mul_right'
  given: [MulRightReflectLE α] {a b c : α} (bc : b * a <= c * a)
  proof: MulRightReflectLE.le_of_mul_le_mul_right' bc

@[to_additive (attr := simp, to_dual self)]

中文:
定理 le_of_mul_le_mul_right'
  条件: [MulRightReflectLE α] {a b c : α} (bc : b * a <= c * a)
  证明: MulRightReflectLE.le_of_mul_le_mul_right' bc

@[to_additive (attr := simp, to_dual self)]

Depends on / 依赖: MulRightReflectLE, MulRightReflectLE.le_of_mul_le_mul_right, le_of_mul_le_mul_right
-/
theorem le_of_mul_le_mul_right' [MulRightReflectLE α] {a b c : α} (bc : b * a <= c * a) :
    b <= c :=
  MulRightReflectLE.le_of_mul_le_mul_right' bc

@[to_additive (attr := simp, to_dual self)]
/--
theorem `mul_le_mul_iff_left` / 定理 `mul_le_mul_iff_left`

English:
theorem mul_le_mul_iff_left
  given: [MulLeftMono α] [MulLeftReflectLE α] (a : α) {b c : α}
  proof: rel_iff_cov' ‹MulLeftMono α›.elim fun _ => MulLeftReflectLE.le_of_mul_le_mul_left'

@[to_additive (attr := simp, to_dual self)]

中文:
定理 mul_le_mul_iff_left
  条件: [MulLeftMono α] [MulLeftReflectLE α] (a : α) {b c : α}
  证明: rel_iff_cov' ‹MulLeftMono α›.elim fun _ => MulLeftReflectLE.le_of_mul_le_mul_left'

@[to_additive (attr := simp, to_dual self)]

Depends on / 依赖: MulLeftMono, MulLeftReflectLE, MulLeftReflectLE.le_of_mul_le_mul_left, le_of_mul_le_mul_left, rel_iff_cov
-/
theorem mul_le_mul_iff_left [MulLeftMono α] [MulLeftReflectLE α] (a : α) {b c : α} :
    a * b <= a * c ↔ b <= c :=
  rel_iff_cov' ‹MulLeftMono α›.elim fun _ => MulLeftReflectLE.le_of_mul_le_mul_left'

@[to_additive (attr := simp, to_dual self)]
/--
theorem `mul_le_mul_iff_right` / 定理 `mul_le_mul_iff_right`

English:
theorem mul_le_mul_iff_right
  given: [MulRightMono α] [MulRightReflectLE α] (a : α) {b c : α}
  proof: rel_iff_cov' ‹MulRightMono α›.elim fun _ => MulRightReflectLE.le_of_mul_le_mul_right'

中文:
定理 mul_le_mul_iff_right
  条件: [MulRightMono α] [MulRightReflectLE α] (a : α) {b c : α}
  证明: rel_iff_cov' ‹MulRightMono α›.elim fun _ => MulRightReflectLE.le_of_mul_le_mul_right'

Depends on / 依赖: MulRightMono, MulRightReflectLE, MulRightReflectLE.le_of_mul_le_mul_right, le_of_mul_le_mul_right, rel_iff_cov
-/
theorem mul_le_mul_iff_right [MulRightMono α] [MulRightReflectLE α] (a : α) {b c : α} :
    b * a <= c * a ↔ b <= c :=
  rel_iff_cov' ‹MulRightMono α›.elim fun _ => MulRightReflectLE.le_of_mul_le_mul_right'

end LE

section LT

variable [LT α]

@[to_additive (attr := simp, to_dual self)]
/--
theorem `mul_lt_mul_iff_left` / 定理 `mul_lt_mul_iff_left`

English:
theorem mul_lt_mul_iff_left
  statement: [MulLeftStrictMono α]
  proof: rel_iff_cov α α (· * ·) (· < ·) a

@[to_additive (attr := simp, to_dual self)]

中文:
定理 mul_lt_mul_iff_left
  结论: [MulLeftStrictMono α]
  证明: rel_iff_cov α α (· * ·) (· < ·) a

@[to_additive (attr := simp, to_dual self)]

Depends on / 依赖: rel_iff_cov
-/
theorem mul_lt_mul_iff_left [MulLeftStrictMono α]
    [MulLeftReflectLT α] (a : α) {b c : α} :
    a * b < a * c ↔ b < c :=
  rel_iff_cov α α (· * ·) (· < ·) a

@[to_additive (attr := simp, to_dual self)]
/--
theorem `mul_lt_mul_iff_right` / 定理 `mul_lt_mul_iff_right`

English:
theorem mul_lt_mul_iff_right
  statement: [MulRightStrictMono α]
  proof: rel_iff_cov α α (swap (· * ·)) (· < ·) a

中文:
定理 mul_lt_mul_iff_right
  结论: [MulRightStrictMono α]
  证明: rel_iff_cov α α (swap (· * ·)) (· < ·) a

Depends on / 依赖: rel_iff_cov
-/
theorem mul_lt_mul_iff_right [MulRightStrictMono α]
    [MulRightReflectLT α] (a : α) {b c : α} :
    b * a < c * a ↔ b < c :=
  rel_iff_cov α α (swap (· * ·)) (· < ·) a

-- Note: in this section, we use `@[gcongr high]` so that these lemmas have a higher priority than
-- lemmas like `mul_lt_mul_of_pos_left`, which have an extra side condition.

@[to_additive (attr := gcongr high, to_dual self)]
/--
theorem `mul_lt_mul_right` / 定理 `mul_lt_mul_right`

English:
theorem mul_lt_mul_right
  given: [MulLeftStrictMono α] {b c : α} (bc : b < c) (a : α)
  proof: CovariantClass.elim _ bc

@[to_additive (attr := to_dual self) lt_of_add_lt_add_left]

中文:
定理 mul_lt_mul_right
  条件: [MulLeftStrictMono α] {b c : α} (bc : b < c) (a : α)
  证明: CovariantClass.elim _ bc

@[to_additive (attr := to_dual self) lt_of_add_lt_add_left]

Depends on / 依赖: CovariantClass, CovariantClass.elim
-/
theorem mul_lt_mul_right [MulLeftStrictMono α] {b c : α} (bc : b < c) (a : α) :
    a * b < a * c :=
  CovariantClass.elim _ bc

@[to_additive (attr := to_dual self) lt_of_add_lt_add_left]
/--
theorem `lt_of_mul_lt_mul_left'` / 定理 `lt_of_mul_lt_mul_left'`

English:
theorem lt_of_mul_lt_mul_left'
  statement: [MulLeftReflectLT α] {a b c : α}
  proof: ContravariantClass.elim _ bc

@[to_additive (attr := gcongr high, to_dual self)]

中文:
定理 lt_of_mul_lt_mul_left'
  结论: [MulLeftReflectLT α] {a b c : α}
  证明: ContravariantClass.elim _ bc

@[to_additive (attr := gcongr high, to_dual self)]

Depends on / 依赖: ContravariantClass, ContravariantClass.elim
-/
theorem lt_of_mul_lt_mul_left' [MulLeftReflectLT α] {a b c : α}
    (bc : a * b < a * c) :
    b < c :=
  ContravariantClass.elim _ bc

@[to_additive (attr := gcongr high, to_dual self)]
/--
theorem `mul_lt_mul_left` / 定理 `mul_lt_mul_left`

English:
theorem mul_lt_mul_left
  statement: [i : MulRightStrictMono α] {b c : α} (bc : b < c)
  proof: i.elim a bc

@[to_additive (attr := to_dual self) lt_of_add_lt_add_right]

中文:
定理 mul_lt_mul_left
  结论: [i : MulRightStrictMono α] {b c : α} (bc : b < c)
  证明: i.elim a bc

@[to_additive (attr := to_dual self) lt_of_add_lt_add_right]

Depends on / 依赖: i.elim
-/
theorem mul_lt_mul_left [i : MulRightStrictMono α] {b c : α} (bc : b < c)
    (a : α) :
    b * a < c * a :=
  i.elim a bc

@[to_additive (attr := to_dual self) lt_of_add_lt_add_right]
/--
theorem `lt_of_mul_lt_mul_right'` / 定理 `lt_of_mul_lt_mul_right'`

English:
theorem lt_of_mul_lt_mul_right'
  statement: [i : MulRightReflectLT α] {a b c : α}
  proof: i.elim a bc

中文:
定理 lt_of_mul_lt_mul_right'
  结论: [i : MulRightReflectLT α] {a b c : α}
  证明: i.elim a bc

Depends on / 依赖: i.elim
-/
theorem lt_of_mul_lt_mul_right' [i : MulRightReflectLT α] {a b c : α}
    (bc : b * a < c * a) :
    b < c :=
  i.elim a bc

end LT

section Preorder

variable [Preorder α]

@[to_additive]
/--
lemma `mul_right_mono` / 引理 `mul_right_mono`

English:
lemma mul_right_mono
  given: [MulLeftMono α] {a : α}
  statement: Monotone (a * ·)
  proof: fun _ _ h => mul_le_mul_right h _

@[to_additive]

中文:
引理 mul_right_mono
  条件: [MulLeftMono α] {a : α}
  结论: 递增 (a * ·)
  证明: fun _ _ h => mul_le_mul_right h _

@[to_additive]

Depends on / 依赖: mul_le_mul_right
-/
lemma mul_right_mono [MulLeftMono α] {a : α} : Monotone (a * ·) :=
  fun _ _ h => mul_le_mul_right h _

@[to_additive]
/--
lemma `mul_left_mono` / 引理 `mul_left_mono`

English:
lemma mul_left_mono
  given: [MulRightMono α] {a : α}
  statement: Monotone (· * a)
  proof: fun _ _ h => mul_le_mul_left h _

@[to_additive]

中文:
引理 mul_left_mono
  条件: [MulRightMono α] {a : α}
  结论: 递增 (· * a)
  证明: fun _ _ h => mul_le_mul_left h _

@[to_additive]

Depends on / 依赖: mul_le_mul_left
-/
lemma mul_left_mono [MulRightMono α] {a : α} : Monotone (· * a) :=
  fun _ _ h => mul_le_mul_left h _

@[to_additive]
/--
lemma `mul_right_strictMono` / 引理 `mul_right_strictMono`

English:
lemma mul_right_strictMono
  given: [MulLeftStrictMono α] {a : α}
  statement: StrictMono (a * ·)
  proof: fun _ _ h => mul_lt_mul_right h _

@[to_additive]

中文:
引理 mul_right_strictMono
  条件: [MulLeftStrictMono α] {a : α}
  结论: 严格递增 (a * ·)
  证明: fun _ _ h => mul_lt_mul_right h _

@[to_additive]

Depends on / 依赖: mul_lt_mul_right
-/
lemma mul_right_strictMono [MulLeftStrictMono α] {a : α} : StrictMono (a * ·) :=
  fun _ _ h => mul_lt_mul_right h _

@[to_additive]
/--
lemma `mul_left_strictMono` / 引理 `mul_left_strictMono`

English:
lemma mul_left_strictMono
  given: [MulRightStrictMono α] {a : α}
  statement: StrictMono (· * a)
  proof: fun _ _ h => mul_lt_mul_left h _

中文:
引理 mul_left_strictMono
  条件: [MulRightStrictMono α] {a : α}
  结论: 严格递增 (· * a)
  证明: fun _ _ h => mul_lt_mul_left h _

Depends on / 依赖: mul_lt_mul_left
-/
lemma mul_left_strictMono [MulRightStrictMono α] {a : α} : StrictMono (· * a) :=
  fun _ _ h => mul_lt_mul_left h _

-- Note: in this section, we use `@[gcongr high]` so that these lemmas have a higher priority than
-- lemmas like `mul_le_mul_of_nonneg`, which have an extra side condition.

@[to_additive (attr := gcongr high, to_dual self)]
/--
theorem `mul_lt_mul_of_lt_of_lt` / 定理 `mul_lt_mul_of_lt_of_lt`

English:
theorem mul_lt_mul_of_lt_of_lt
  statement: [MulLeftStrictMono α]
  proof: calc
    a * c < a * d := mul_lt_mul_right h₂ a
    _ < b * d := mul_lt_mul_left h₁ d

@[to_dual self] alias add_lt_add := add_lt_add_of_lt_of_lt

@[to_additive (attr := to_dual self)]

中文:
定理 mul_lt_mul_of_lt_of_lt
  结论: [MulLeftStrictMono α]
  证明: calc
    a * c < a * d := mul_lt_mul_right h₂ a
    _ < b * d := mul_lt_mul_left h₁ d

@[to_dual self] alias add_lt_add := add_lt_add_of_lt_of_lt

@[to_additive (attr := to_dual self)]

Depends on / 依赖: mul_lt_mul_left, mul_lt_mul_right
-/
theorem mul_lt_mul_of_lt_of_lt [MulLeftStrictMono α]
    [MulRightStrictMono α]
    {a b c d : α} (h₁ : a < b) (h₂ : c < d) : a * c < b * d :=
  calc
    a * c < a * d := mul_lt_mul_right h₂ a
    _ < b * d := mul_lt_mul_left h₁ d

@[to_dual self] alias add_lt_add := add_lt_add_of_lt_of_lt

@[to_additive (attr := to_dual self)]
/--
theorem `mul_lt_mul_of_le_of_lt` / 定理 `mul_lt_mul_of_le_of_lt`

English:
theorem mul_lt_mul_of_le_of_lt
  statement: [MulLeftStrictMono α]
  proof: (mul_le_mul_left h₁ _).trans_lt (mul_lt_mul_right h₂ b)

@[to_additive (attr := to_dual self)]

中文:
定理 mul_lt_mul_of_le_of_lt
  结论: [MulLeftStrictMono α]
  证明: (mul_le_mul_left h₁ _).trans_lt (mul_lt_mul_right h₂ b)

@[to_additive (attr := to_dual self)]

Depends on / 依赖: mul_le_mul_left, mul_lt_mul_right, trans_lt
-/
theorem mul_lt_mul_of_le_of_lt [MulLeftStrictMono α]
    [MulRightMono α] {a b c d : α} (h₁ : a <= b) (h₂ : c < d) :
    a * c < b * d :=
  (mul_le_mul_left h₁ _).trans_lt (mul_lt_mul_right h₂ b)

@[to_additive (attr := to_dual self)]
/--
theorem `mul_lt_mul_of_lt_of_le` / 定理 `mul_lt_mul_of_lt_of_le`

English:
theorem mul_lt_mul_of_lt_of_le
  statement: [MulLeftMono α]
  proof: (mul_le_mul_right h₂ _).trans_lt (mul_lt_mul_left h₁ d)

中文:
定理 mul_lt_mul_of_lt_of_le
  结论: [MulLeftMono α]
  证明: (mul_le_mul_right h₂ _).trans_lt (mul_lt_mul_left h₁ d)

Depends on / 依赖: mul_le_mul_right, mul_lt_mul_left, trans_lt
-/
theorem mul_lt_mul_of_lt_of_le [MulLeftMono α]
    [MulRightStrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c <= d) :
    a * c < b * d :=
  (mul_le_mul_right h₂ _).trans_lt (mul_lt_mul_left h₁ d)

/-- Only assumes left strict covariance. -/
@[to_additive (attr := to_dual self) /-- Only assumes left strict covariance -/]
/--
theorem `Left.mul_lt_mul` / 定理 `Left.mul_lt_mul`

English:
theorem Left.mul_lt_mul
  statement: [MulLeftStrictMono α]
  proof: mul_lt_mul_of_le_of_lt h₁.le h₂

中文:
定理 Left.mul_lt_mul
  结论: [MulLeftStrictMono α]
  证明: mul_lt_mul_of_le_of_lt h₁.le h₂

Depends on / 依赖: mul_lt_mul_of_le_of_lt
-/
theorem Left.mul_lt_mul [MulLeftStrictMono α]
    [MulRightMono α] {a b c d : α} (h₁ : a < b) (h₂ : c < d) :
    a * c < b * d :=
  mul_lt_mul_of_le_of_lt h₁.le h₂

/-- Only assumes right strict covariance. -/
@[to_additive (attr := to_dual self) /-- Only assumes right strict covariance -/]
/--
theorem `Right.mul_lt_mul` / 定理 `Right.mul_lt_mul`

English:
theorem Right.mul_lt_mul
  statement: [MulLeftMono α]
  proof: mul_lt_mul_of_lt_of_le h₁ h₂.le

@[to_additive (attr := gcongr high, to_dual self) add_le_add]

中文:
定理 Right.mul_lt_mul
  结论: [MulLeftMono α]
  证明: mul_lt_mul_of_lt_of_le h₁ h₂.le

@[to_additive (attr := gcongr high, to_dual self) add_le_add]

Depends on / 依赖: mul_lt_mul_of_lt_of_le
-/
theorem Right.mul_lt_mul [MulLeftMono α]
    [MulRightStrictMono α] {a b c d : α}
    (h₁ : a < b) (h₂ : c < d) :
    a * c < b * d :=
  mul_lt_mul_of_lt_of_le h₁ h₂.le

@[to_additive (attr := gcongr high, to_dual self) add_le_add]
/--
theorem `mul_le_mul'` / 定理 `mul_le_mul'`

English:
theorem mul_le_mul'
  statement: [MulLeftMono α] [MulRightMono α]
  proof: by grw [h₁, h₂]

@[to_additive (attr := to_dual self)]

中文:
定理 mul_le_mul'
  结论: [MulLeftMono α] [MulRightMono α]
  证明: by grw [h₁, h₂]

@[to_additive (attr := to_dual self)]
-/
theorem mul_le_mul' [MulLeftMono α] [MulRightMono α]
    {a b c d : α} (h₁ : a <= b) (h₂ : c <= d) :
    a * c <= b * d := by grw [h₁, h₂]

@[to_additive (attr := to_dual self)]
/--
theorem `mul_le_mul_three` / 定理 `mul_le_mul_three`

English:
theorem mul_le_mul_three
  statement: [MulLeftMono α]
  proof: mul_le_mul' (mul_le_mul' h₁ h₂) h₃

@[to_additive]

中文:
定理 mul_le_mul_three
  结论: [MulLeftMono α]
  证明: mul_le_mul' (mul_le_mul' h₁ h₂) h₃

@[to_additive]

Depends on / 依赖: mul_le_mul
-/
theorem mul_le_mul_three [MulLeftMono α]
    [MulRightMono α] {a b c d e f : α} (h₁ : a <= d) (h₂ : b <= e)
    (h₃ : c <= f) :
    a * b * c <= d * e * f :=
  mul_le_mul' (mul_le_mul' h₁ h₂) h₃

@[to_additive]
/--
theorem `mul_lt_of_mul_lt_left` / 定理 `mul_lt_of_mul_lt_left`

English:
theorem mul_lt_of_mul_lt_left
  statement: [MulLeftMono α] {a b c d : α} (h : a * b < c)
  proof: (mul_le_mul_right hle a).trans_lt h

@[to_additive]

中文:
定理 mul_lt_of_mul_lt_left
  结论: [MulLeftMono α] {a b c d : α} (h : a * b < c)
  证明: (mul_le_mul_right hle a).trans_lt h

@[to_additive]

Depends on / 依赖: mul_le_mul_right, trans_lt
-/
theorem mul_lt_of_mul_lt_left [MulLeftMono α] {a b c d : α} (h : a * b < c)
    (hle : d <= b) :
    a * d < c :=
  (mul_le_mul_right hle a).trans_lt h

@[to_additive]
/--
theorem `mul_le_of_mul_le_left` / 定理 `mul_le_of_mul_le_left`

English:
theorem mul_le_of_mul_le_left
  statement: [MulLeftMono α] {a b c d : α} (h : a * b <= c)
  proof: @act_rel_of_rel_of_act_rel _ _ _ (· <= ·) _ _ a _ _ _ hle h

@[to_additive]

中文:
定理 mul_le_of_mul_le_left
  结论: [MulLeftMono α] {a b c d : α} (h : a * b <= c)
  证明: @act_rel_of_rel_of_act_rel _ _ _ (· <= ·) _ _ a _ _ _ hle h

@[to_additive]

Depends on / 依赖: act_rel_of_rel_of_act_rel
-/
theorem mul_le_of_mul_le_left [MulLeftMono α] {a b c d : α} (h : a * b <= c)
    (hle : d <= b) :
    a * d <= c :=
  @act_rel_of_rel_of_act_rel _ _ _ (· <= ·) _ _ a _ _ _ hle h

@[to_additive]
/--
theorem `mul_lt_of_mul_lt_right` / 定理 `mul_lt_of_mul_lt_right`

English:
theorem mul_lt_of_mul_lt_right
  statement: [MulRightMono α] {a b c d : α}
  proof: (mul_le_mul_left hle b).trans_lt h

@[to_additive]

中文:
定理 mul_lt_of_mul_lt_right
  结论: [MulRightMono α] {a b c d : α}
  证明: (mul_le_mul_left hle b).trans_lt h

@[to_additive]

Depends on / 依赖: mul_le_mul_left, trans_lt
-/
theorem mul_lt_of_mul_lt_right [MulRightMono α] {a b c d : α}
    (h : a * b < c) (hle : d <= a) :
    d * b < c :=
  (mul_le_mul_left hle b).trans_lt h

@[to_additive]
/--
theorem `mul_le_of_mul_le_right` / 定理 `mul_le_of_mul_le_right`

English:
theorem mul_le_of_mul_le_right
  statement: [MulRightMono α] {a b c d : α}
  proof: (mul_le_mul_left hle b).trans h

@[to_additive]

中文:
定理 mul_le_of_mul_le_right
  结论: [MulRightMono α] {a b c d : α}
  证明: (mul_le_mul_left hle b).trans h

@[to_additive]

Depends on / 依赖: mul_le_mul_left
-/
theorem mul_le_of_mul_le_right [MulRightMono α] {a b c d : α}
    (h : a * b <= c) (hle : d <= a) :
    d * b <= c :=
  (mul_le_mul_left hle b).trans h

@[to_additive]
/--
theorem `lt_mul_of_lt_mul_left` / 定理 `lt_mul_of_lt_mul_left`

English:
theorem lt_mul_of_lt_mul_left
  statement: [MulLeftMono α] {a b c d : α} (h : a < b * c)
  proof: h.trans_le (mul_le_mul_right hle b)

@[to_additive]

中文:
定理 lt_mul_of_lt_mul_left
  结论: [MulLeftMono α] {a b c d : α} (h : a < b * c)
  证明: h.trans_le (mul_le_mul_right hle b)

@[to_additive]

Depends on / 依赖: h.trans_le, mul_le_mul_right, trans_le
-/
theorem lt_mul_of_lt_mul_left [MulLeftMono α] {a b c d : α} (h : a < b * c)
    (hle : c <= d) :
    a < b * d :=
  h.trans_le (mul_le_mul_right hle b)

@[to_additive]
/--
theorem `le_mul_of_le_mul_left` / 定理 `le_mul_of_le_mul_left`

English:
theorem le_mul_of_le_mul_left
  statement: [MulLeftMono α] {a b c d : α} (h : a <= b * c)
  proof: @rel_act_of_rel_of_rel_act _ _ _ (· <= ·) _ _ b _ _ _ hle h

@[to_additive]

中文:
定理 le_mul_of_le_mul_left
  结论: [MulLeftMono α] {a b c d : α} (h : a <= b * c)
  证明: @rel_act_of_rel_of_rel_act _ _ _ (· <= ·) _ _ b _ _ _ hle h

@[to_additive]

Depends on / 依赖: rel_act_of_rel_of_rel_act
-/
theorem le_mul_of_le_mul_left [MulLeftMono α] {a b c d : α} (h : a <= b * c)
    (hle : c <= d) :
    a <= b * d :=
  @rel_act_of_rel_of_rel_act _ _ _ (· <= ·) _ _ b _ _ _ hle h

@[to_additive]
/--
theorem `lt_mul_of_lt_mul_right` / 定理 `lt_mul_of_lt_mul_right`

English:
theorem lt_mul_of_lt_mul_right
  statement: [MulRightMono α] {a b c d : α}
  proof: h.trans_le (mul_le_mul_left hle c)

@[to_additive]

中文:
定理 lt_mul_of_lt_mul_right
  结论: [MulRightMono α] {a b c d : α}
  证明: h.trans_le (mul_le_mul_left hle c)

@[to_additive]

Depends on / 依赖: h.trans_le, mul_le_mul_left, trans_le
-/
theorem lt_mul_of_lt_mul_right [MulRightMono α] {a b c d : α}
    (h : a < b * c) (hle : b <= d) :
    a < d * c :=
  h.trans_le (mul_le_mul_left hle c)

@[to_additive]
/--
theorem `le_mul_of_le_mul_right` / 定理 `le_mul_of_le_mul_right`

English:
theorem le_mul_of_le_mul_right
  statement: [MulRightMono α] {a b c d : α}
  proof: h.trans (mul_le_mul_left hle c)

中文:
定理 le_mul_of_le_mul_right
  结论: [MulRightMono α] {a b c d : α}
  证明: h.trans (mul_le_mul_left hle c)

Depends on / 依赖: h.trans, mul_le_mul_left
-/
theorem le_mul_of_le_mul_right [MulRightMono α] {a b c d : α}
    (h : a <= b * c) (hle : b <= d) :
    a <= d * c :=
  h.trans (mul_le_mul_left hle c)

end Preorder

section PartialOrder

variable [PartialOrder α]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulLeftReflectLE
  signature: α] : IsLeftCancelMul α where
  body: (le_of_mul_le_mul_left' h.le).antisymm (le_of_mul_le_mul_left' h.ge)

@[deprecated (since := "2026-03-14")]
alias add_left_cancel'' := add_left_cancel
@[to_additive existing, deprecated (since := "2026-03-14")]
alias mul_left_cancel'' := mul_left_cancel

@[to_additive]

中文:
实例 [MulLeftReflectLE
  签名: α] : 左乘消去 α where
  定义体: (le_of_mul_le_mul_left' h.le).antisymm (le_of_mul_le_mul_left' h.ge)

@[deprecated (since := "2026-03-14")]
alias add_left_cancel'' := add_left_cancel
@[to_additive existing, deprecated (since := "2026-03-14")]
alias mul_left_cancel'' := mul_left_cancel

@[to_additive]

Depends on / 依赖: antisymm, h.ge, h.le, le_of_mul_le_mul_left
-/
instance [MulLeftReflectLE α] : IsLeftCancelMul α where
  mul_left_cancel _ _ _ h := (le_of_mul_le_mul_left' h.le).antisymm (le_of_mul_le_mul_left' h.ge)

@[deprecated (since := "2026-03-14")]
alias add_left_cancel'' := add_left_cancel
@[to_additive existing, deprecated (since := "2026-03-14")]
alias mul_left_cancel'' := mul_left_cancel

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulRightReflectLE
  signature: α] : IsRightCancelMul α where
  body: (le_of_mul_le_mul_right' h.le).antisymm (le_of_mul_le_mul_right' h.ge)

@[deprecated (since := "2026-03-14")]
alias add_right_cancel'' := add_right_cancel
@[to_additive existing, deprecated (since := "2026-03-14")]
alias mul_right_cancel'' := mul_right_cancel

中文:
实例 [MulRightReflectLE
  签名: α] : 右乘消去 α where
  定义体: (le_of_mul_le_mul_right' h.le).antisymm (le_of_mul_le_mul_right' h.ge)

@[deprecated (since := "2026-03-14")]
alias add_right_cancel'' := add_right_cancel
@[to_additive existing, deprecated (since := "2026-03-14")]
alias mul_right_cancel'' := mul_right_cancel

Depends on / 依赖: antisymm, h.ge, h.le, le_of_mul_le_mul_right
-/
instance [MulRightReflectLE α] : IsRightCancelMul α where
  mul_right_cancel _ _ _ h := (le_of_mul_le_mul_right' h.le).antisymm (le_of_mul_le_mul_right' h.ge)

@[deprecated (since := "2026-03-14")]
alias add_right_cancel'' := add_right_cancel
@[to_additive existing, deprecated (since := "2026-03-14")]
alias mul_right_cancel'' := mul_right_cancel

/--
lemma `mul_le_mul_iff_of_ge` / 引理 `mul_le_mul_iff_of_ge`

English:
lemma mul_le_mul_iff_of_ge
  statement: [MulLeftStrictMono α]
  proof: by
  have := mulLeftMono_of_mulLeftStrictMono α
  have := mulRightMono_of_mulRightStrictMono α
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, ha, hb, true_and]
  refine ⟨fun ha => h.not_gt ?_, fun hb => h.not_gt ?_⟩
  exacts [mul_lt_mul_of_lt_of_le ha hb, mul_lt_mul

中文:
引理 mul_le_mul_iff_of_ge
  结论: [MulLeftStrictMono α]
  证明: by
  have := mulLeftMono_of_mulLeftStrictMono α
  have := mulRightMono_of_mulRightStrictMono α
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, ha, hb, true_and]
  refine ⟨fun ha => h.not_gt ?_, fun hb => h.not_gt ?_⟩
  exacts [mul_lt_mul_of_lt_of_le ha hb, mul_lt_mul
-/
@[to_additive] lemma mul_le_mul_iff_of_ge [MulLeftStrictMono α]
    [MulRightStrictMono α] {a₁ a₂ b₁ b₂ : α} (ha : a₁ <= a₂) (hb : b₁ <= b₂) :
    a₂ * b₂ <= a₁ * b₁ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  have := mulLeftMono_of_mulLeftStrictMono α
  have := mulRightMono_of_mulRightStrictMono α
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, ha, hb, true_and]
  refine ⟨fun ha => h.not_gt ?_, fun hb => h.not_gt ?_⟩
  exacts [mul_lt_mul_of_lt_of_le ha hb, mul_lt_mul_of_le_of_lt ha hb]

/--
theorem `mul_eq_mul_iff_eq_and_eq` / 定理 `mul_eq_mul_iff_eq_and_eq`

English:
theorem mul_eq_mul_iff_eq_and_eq
  statement: [MulLeftStrictMono α]
  proof: by
  have := mulLeftMono_of_mulLeftStrictMono α
  have := mulRightMono_of_mulRightStrictMono α
  rw [le_antisymm_iff]; rw [eq_true (mul_le_mul' hac hbd)]; rw [true_and]; rw [mul_le_mul_iff_of_ge hac hbd]

@[to_additive]

中文:
定理 mul_eq_mul_iff_eq_and_eq
  结论: [MulLeftStrictMono α]
  证明: by
  have := mulLeftMono_of_mulLeftStrictMono α
  have := mulRightMono_of_mulRightStrictMono α
  rw [le_antisymm_iff]; rw [eq_true (mul_le_mul' hac hbd)]; rw [true_and]; rw [mul_le_mul_iff_of_ge hac hbd]

@[to_additive]
-/
@[to_additive] theorem mul_eq_mul_iff_eq_and_eq [MulLeftStrictMono α]
    [MulRightStrictMono α] {a b c d : α} (hac : a <= c) (hbd : b <= d) :
    a * b = c * d ↔ a = c ∧ b = d := by
  have := mulLeftMono_of_mulLeftStrictMono α
  have := mulRightMono_of_mulRightStrictMono α
  rw [le_antisymm_iff]; rw [eq_true (mul_le_mul' hac hbd)]; rw [true_and]; rw [mul_le_mul_iff_of_ge hac hbd]

@[to_additive]
/--
lemma `mul_left_inj_of_comparable` / 引理 `mul_left_inj_of_comparable`

English:
lemma mul_left_inj_of_comparable
  given: [MulRightStrictMono α] {a b c : α} (h : b <= c ∨ c <= b)
  proof: by
  refine ⟨fun h' => ?_, (· ▸ rfl)⟩
  contrapose h'
  obtain h | h := h
.ne' · exact mul_lt_mul_left (h.lt_of_ne' h') a
.ne · exact mul_lt_mul_left (h.lt_of_ne h') a

@[to_additive]

中文:
引理 mul_left_inj_of_comparable
  条件: [MulRightStrictMono α] {a b c : α} (h : b <= c ∨ c <= b)
  证明: by
  refine ⟨fun h' => ?_, (· ▸ rfl)⟩
  contrapose h'
  obtain h | h := h
.ne' · exact mul_lt_mul_left (h.lt_of_ne' h') a
.ne · exact mul_lt_mul_left (h.lt_of_ne h') a

@[to_additive]

Depends on / 依赖: contrapose, h.lt_of_ne, lt_of_ne, mul_lt_mul_left
-/
lemma mul_left_inj_of_comparable [MulRightStrictMono α] {a b c : α} (h : b <= c ∨ c <= b) :
    c * a = b * a ↔ c = b := by
  refine ⟨fun h' => ?_, (· ▸ rfl)⟩
  contrapose h'
  obtain h | h := h
.ne' · exact mul_lt_mul_left (h.lt_of_ne' h') a
.ne · exact mul_lt_mul_left (h.lt_of_ne h') a

@[to_additive]
/--
lemma `mul_right_inj_of_comparable` / 引理 `mul_right_inj_of_comparable`

English:
lemma mul_right_inj_of_comparable
  given: [MulLeftStrictMono α] {a b c : α} (h : b <= c ∨ c <= b)
  proof: by
  refine ⟨fun h' => ?_, (· ▸ rfl)⟩
  contrapose h'
  obtain h | h := h
.ne' · exact mul_lt_mul_right (h.lt_of_ne' h') a
.ne · exact mul_lt_mul_right (h.lt_of_ne h') a

中文:
引理 mul_right_inj_of_comparable
  条件: [MulLeftStrictMono α] {a b c : α} (h : b <= c ∨ c <= b)
  证明: by
  refine ⟨fun h' => ?_, (· ▸ rfl)⟩
  contrapose h'
  obtain h | h := h
.ne' · exact mul_lt_mul_right (h.lt_of_ne' h') a
.ne · exact mul_lt_mul_right (h.lt_of_ne h') a

Depends on / 依赖: contrapose, h.lt_of_ne, lt_of_ne, mul_lt_mul_right
-/
lemma mul_right_inj_of_comparable [MulLeftStrictMono α] {a b c : α} (h : b <= c ∨ c <= b) :
    a * c = a * b ↔ c = b := by
  refine ⟨fun h' => ?_, (· ▸ rfl)⟩
  contrapose h'
  obtain h | h := h
.ne' · exact mul_lt_mul_right (h.lt_of_ne' h') a
.ne · exact mul_lt_mul_right (h.lt_of_ne h') a

end PartialOrder

section LinearOrder
variable [LinearOrder α] {a b c d : α}

@[to_additive]
/--
theorem `trichotomy_of_mul_eq_mul` / 定理 `trichotomy_of_mul_eq_mul`

English:
theorem trichotomy_of_mul_eq_mul
  proof: by
  obtain hac | rfl | hca := lt_trichotomy a c
  · grind
.1 h · left; simpa using mul_right_inj_of_comparable (le_total d b)
  · obtain hbd | rfl | hdb := lt_trichotomy b d
    · grind
· exact False.elim ne_of_lt (mul_lt_mul_left hca b) h.symm
· exact False.elim ne_of_lt (mul_lt_mul_of_lt_of_lt hc

中文:
定理 trichotomy_of_mul_eq_mul
  证明: by
  obtain hac | rfl | hca := lt_trichotomy a c
  · grind
.1 h · left; simpa using mul_right_inj_of_comparable (le_total d b)
  · obtain hbd | rfl | hdb := lt_trichotomy b d
    · grind
· exact False.elim ne_of_lt (mul_lt_mul_left hca b) h.symm
· exact False.elim ne_of_lt (mul_lt_mul_of_lt_of_lt hc

Depends on / 依赖: False.elim, h.symm, le_total, lt_trichotomy, mul_lt_mul_left, mul_lt_mul_of_lt_of_lt, mul_right_inj_of_comparable, ne_of_lt
-/
theorem trichotomy_of_mul_eq_mul
    [MulLeftStrictMono α] [MulRightStrictMono α]
    (h : a * b = c * d) : (a = c ∧ b = d) ∨ a < c ∨ b < d := by
  obtain hac | rfl | hca := lt_trichotomy a c
  · grind
.1 h · left; simpa using mul_right_inj_of_comparable (le_total d b)
  · obtain hbd | rfl | hdb := lt_trichotomy b d
    · grind
· exact False.elim ne_of_lt (mul_lt_mul_left hca b) h.symm
· exact False.elim ne_of_lt (mul_lt_mul_of_lt_of_lt hca hdb) h.symm

@[to_additive]
/--
lemma `mul_max` / 引理 `mul_max`

English:
lemma mul_max
  given: [MulLeftMono α] (a b c : α)
  proof: mul_right_mono.map_max

@[to_additive]

中文:
引理 mul_max
  条件: [MulLeftMono α] (a b c : α)
  证明: mul_right_mono.map_max

@[to_additive]

Depends on / 依赖: map_max, mul_right_mono, mul_right_mono.map_max
-/
lemma mul_max [MulLeftMono α] (a b c : α) :
    a * max b c = max (a * b) (a * c) := mul_right_mono.map_max

@[to_additive]
/--
lemma `max_mul` / 引理 `max_mul`

English:
lemma max_mul
  given: [MulRightMono α] (a b c : α)
  proof: mul_left_mono.map_max

@[to_additive]

中文:
引理 max_mul
  条件: [MulRightMono α] (a b c : α)
  证明: mul_left_mono.map_max

@[to_additive]

Depends on / 依赖: map_max, mul_left_mono, mul_left_mono.map_max
-/
lemma max_mul [MulRightMono α] (a b c : α) :
    max a b * c = max (a * c) (b * c) := mul_left_mono.map_max

@[to_additive]
/--
lemma `mul_min` / 引理 `mul_min`

English:
lemma mul_min
  given: [MulLeftMono α] (a b c : α)
  proof: mul_right_mono.map_min

@[to_additive]

中文:
引理 mul_min
  条件: [MulLeftMono α] (a b c : α)
  证明: mul_right_mono.map_min

@[to_additive]

Depends on / 依赖: map_min, mul_right_mono, mul_right_mono.map_min
-/
lemma mul_min [MulLeftMono α] (a b c : α) :
    a * min b c = min (a * b) (a * c) := mul_right_mono.map_min

@[to_additive]
/--
lemma `min_mul` / 引理 `min_mul`

English:
lemma min_mul
  given: [MulRightMono α] (a b c : α)
  proof: mul_left_mono.map_min

中文:
引理 min_mul
  条件: [MulRightMono α] (a b c : α)
  证明: mul_left_mono.map_min

Depends on / 依赖: map_min, mul_left_mono, mul_left_mono.map_min
-/
lemma min_mul [MulRightMono α] (a b c : α) :
    min a b * c = min (a * c) (b * c) := mul_left_mono.map_min

/--
lemma `min_lt_max_of_mul_lt_mul` / 引理 `min_lt_max_of_mul_lt_mul`

English:
lemma min_lt_max_of_mul_lt_mul
  proof: by
  simp_rw [min_lt_iff, lt_max_iff]; contrapose! h; exact mul_le_mul' h.1.1 h.2.2

中文:
引理 min_lt_max_of_mul_lt_mul
  证明: by
  simp_rw [min_lt_iff, lt_max_iff]; contrapose! h; exact mul_le_mul' h.1.1 h.2.2
-/
@[to_additive] lemma min_lt_max_of_mul_lt_mul
    [MulLeftMono α] [MulRightMono α]
    (h : a * b < c * d) : min a b < max c d := by
  simp_rw [min_lt_iff, lt_max_iff]; contrapose! h; exact mul_le_mul' h.1.1 h.2.2

/--
lemma `Left.min_le_max_of_mul_le_mul` / 引理 `Left.min_le_max_of_mul_le_mul`

English:
lemma Left.min_le_max_of_mul_le_mul
  proof: by
  simp_rw [min_le_iff, le_max_iff]; contrapose! h; exact mul_lt_mul_of_le_of_lt h.1.1.le h.2.2

中文:
引理 Left.min_le_max_of_mul_le_mul
  证明: by
  simp_rw [min_le_iff, le_max_iff]; contrapose! h; exact mul_lt_mul_of_le_of_lt h.1.1.le h.2.2
-/
@[to_additive] lemma Left.min_le_max_of_mul_le_mul
    [MulLeftStrictMono α] [MulRightMono α]
    (h : a * b <= c * d) : min a b <= max c d := by
  simp_rw [min_le_iff, le_max_iff]; contrapose! h; exact mul_lt_mul_of_le_of_lt h.1.1.le h.2.2

/--
lemma `Right.min_le_max_of_mul_le_mul` / 引理 `Right.min_le_max_of_mul_le_mul`

English:
lemma Right.min_le_max_of_mul_le_mul
  proof: by
  simp_rw [min_le_iff, le_max_iff]; contrapose! h; exact mul_lt_mul_of_lt_of_le h.1.1 h.2.2.le

中文:
引理 Right.min_le_max_of_mul_le_mul
  证明: by
  simp_rw [min_le_iff, le_max_iff]; contrapose! h; exact mul_lt_mul_of_lt_of_le h.1.1 h.2.2.le
-/
@[to_additive] lemma Right.min_le_max_of_mul_le_mul
    [MulLeftMono α] [MulRightStrictMono α]
    (h : a * b <= c * d) : min a b <= max c d := by
  simp_rw [min_le_iff, le_max_iff]; contrapose! h; exact mul_lt_mul_of_lt_of_le h.1.1 h.2.2.le

/--
lemma `min_le_max_of_mul_le_mul` / 引理 `min_le_max_of_mul_le_mul`

English:
lemma min_le_max_of_mul_le_mul
  proof: haveI := mulRightMono_of_mulRightStrictMono α
  Left.min_le_max_of_mul_le_mul h

中文:
引理 min_le_max_of_mul_le_mul
  证明: haveI := mulRightMono_of_mulRightStrictMono α
  Left.min_le_max_of_mul_le_mul h
-/
@[to_additive] lemma min_le_max_of_mul_le_mul
    [MulLeftStrictMono α] [MulRightStrictMono α]
    (h : a * b <= c * d) : min a b <= max c d :=
  haveI := mulRightMono_of_mulRightStrictMono α
  Left.min_le_max_of_mul_le_mul h

/-- Not an instance, to avoid loops with `IsLeftCancelMul.mulLeftStrictMono_of_mulLeftMono`. -/
@[to_additive]
/--
theorem `MulLeftStrictMono.toIsLeftCancelMul` / 定理 `MulLeftStrictMono.toIsLeftCancelMul`

English:
theorem MulLeftStrictMono.toIsLeftCancelMul
  given: [MulLeftStrictMono α]
  statement: IsLeftCancelMul α where
  proof: mul_right_strictMono.injective h

中文:
定理 MulLeftStrictMono.toIsLeftCancelMul
  条件: [MulLeftStrictMono α]
  结论: 左乘消去 α where
  证明: mul_right_strictMono.injective h

Depends on / 依赖: injective, mul_right_strictMono, mul_right_strictMono.injective
-/
theorem MulLeftStrictMono.toIsLeftCancelMul [MulLeftStrictMono α] : IsLeftCancelMul α where
  mul_left_cancel _ _ _ h := mul_right_strictMono.injective h

/-- Not an instance, to avoid loops with `IsRightCancelMul.mulRightStrictMono_of_mulRightMono`. -/
@[to_additive]
/--
theorem `MulRightStrictMono.toIsRightCancelMul` / 定理 `MulRightStrictMono.toIsRightCancelMul`

English:
theorem MulRightStrictMono.toIsRightCancelMul
  given: [MulRightStrictMono α]
  statement: IsRightCancelMul α where
  proof: mul_left_strictMono.injective h

中文:
定理 MulRightStrictMono.toIsRightCancelMul
  条件: [MulRightStrictMono α]
  结论: 右乘消去 α where
  证明: mul_left_strictMono.injective h

Depends on / 依赖: injective, mul_left_strictMono, mul_left_strictMono.injective
-/
theorem MulRightStrictMono.toIsRightCancelMul [MulRightStrictMono α] : IsRightCancelMul α where
  mul_right_cancel _ _ _ h := mul_left_strictMono.injective h

end LinearOrder

section LinearOrder
variable [LinearOrder α] [MulLeftMono α] [MulRightMono α] {a b c d : α}

@[to_additive max_add_add_le_max_add_max]
/--
theorem `max_mul_mul_le_max_mul_max'` / 定理 `max_mul_mul_le_max_mul_max'`

English:
theorem max_mul_mul_le_max_mul_max'
  statement: max (a * b) (c * d) <= max a c * max b d
  proof: max_le (mul_le_mul' (le_max_left _ _) <| le_max_left _ _)
mul_le_mul' (le_max_right _ _) le_max_right _ _

@[to_additive min_add_min_le_min_add_add]

中文:
定理 max_mul_mul_le_max_mul_max'
  结论: 最大值 (a * b) (c * d) <= 最大值 a c * 最大值 b d
  证明: max_le (mul_le_mul' (le_max_left _ _) <| le_max_left _ _)
mul_le_mul' (le_max_right _ _) le_max_right _ _

@[to_additive min_add_min_le_min_add_add]

Depends on / 依赖: le_max_left, le_max_right, max_le, mul_le_mul
-/
theorem max_mul_mul_le_max_mul_max' : max (a * b) (c * d) <= max a c * max b d :=
max_le (mul_le_mul' (le_max_left _ _) <| le_max_left _ _)
mul_le_mul' (le_max_right _ _) le_max_right _ _

@[to_additive min_add_min_le_min_add_add]
/--
theorem `min_mul_min_le_min_mul_mul'` / 定理 `min_mul_min_le_min_mul_mul'`

English:
theorem min_mul_min_le_min_mul_mul'
  statement: min a c * min b d <= min (a * b) (c * d)
  proof: le_min (mul_le_mul' (min_le_left _ _) <| min_le_left _ _)
mul_le_mul' (min_le_right _ _) min_le_right _ _

中文:
定理 min_mul_min_le_min_mul_mul'
  结论: 最小值 a c * 最小值 b d <= 最小值 (a * b) (c * d)
  证明: le_min (mul_le_mul' (min_le_left _ _) <| min_le_left _ _)
mul_le_mul' (min_le_right _ _) min_le_right _ _

Depends on / 依赖: le_min, min_le_left, min_le_right, mul_le_mul
-/
theorem min_mul_min_le_min_mul_mul' : min a c * min b d <= min (a * b) (c * d) :=
le_min (mul_le_mul' (min_le_left _ _) <| min_le_left _ _)
mul_le_mul' (min_le_right _ _) min_le_right _ _

end LinearOrder
end Mul

-- using one
section MulOneClass

variable [MulOneClass α]

section LE

variable [LE α]

@[to_additive le_add_of_nonneg_right]
/--
theorem `le_mul_of_one_le_right'` / 定理 `le_mul_of_one_le_right'`

English:
theorem le_mul_of_one_le_right'
  given: [MulLeftMono α] {a b : α} (h : 1 <= b)
  proof: calc
    a = a * 1 := (mul_one a).symm
    _ <= a * b := mul_le_mul_right h a

@[to_additive add_le_of_nonpos_right]

中文:
定理 le_mul_of_one_le_right'
  条件: [MulLeftMono α] {a b : α} (h : 1 <= b)
  证明: calc
    a = a * 1 := (mul_one a).symm
    _ <= a * b := mul_le_mul_right h a

@[to_additive add_le_of_nonpos_right]

Depends on / 依赖: mul_le_mul_right, mul_one
-/
theorem le_mul_of_one_le_right' [MulLeftMono α] {a b : α} (h : 1 <= b) :
    a <= a * b :=
  calc
    a = a * 1 := (mul_one a).symm
    _ <= a * b := mul_le_mul_right h a

@[to_additive add_le_of_nonpos_right]
/--
theorem `mul_le_of_le_one_right'` / 定理 `mul_le_of_le_one_right'`

English:
theorem mul_le_of_le_one_right'
  given: [MulLeftMono α] {a b : α} (h : b <= 1)
  proof: calc
    a * b <= a * 1 := mul_le_mul_right h a
    _ = a := mul_one a

@[to_additive le_add_of_nonneg_left]

中文:
定理 mul_le_of_le_one_right'
  条件: [MulLeftMono α] {a b : α} (h : b <= 1)
  证明: calc
    a * b <= a * 1 := mul_le_mul_right h a
    _ = a := mul_one a

@[to_additive le_add_of_nonneg_left]

Depends on / 依赖: mul_le_mul_right, mul_one
-/
theorem mul_le_of_le_one_right' [MulLeftMono α] {a b : α} (h : b <= 1) :
    a * b <= a :=
  calc
    a * b <= a * 1 := mul_le_mul_right h a
    _ = a := mul_one a

@[to_additive le_add_of_nonneg_left]
/--
theorem `le_mul_of_one_le_left'` / 定理 `le_mul_of_one_le_left'`

English:
theorem le_mul_of_one_le_left'
  given: [MulRightMono α] {a b : α} (h : 1 <= b)
  proof: calc
    a = 1 * a := (one_mul a).symm
    _ <= b * a := mul_le_mul_left h a

@[to_additive add_le_of_nonpos_left]

中文:
定理 le_mul_of_one_le_left'
  条件: [MulRightMono α] {a b : α} (h : 1 <= b)
  证明: calc
    a = 1 * a := (one_mul a).symm
    _ <= b * a := mul_le_mul_left h a

@[to_additive add_le_of_nonpos_left]

Depends on / 依赖: mul_le_mul_left, one_mul
-/
theorem le_mul_of_one_le_left' [MulRightMono α] {a b : α} (h : 1 <= b) :
    a <= b * a :=
  calc
    a = 1 * a := (one_mul a).symm
    _ <= b * a := mul_le_mul_left h a

@[to_additive add_le_of_nonpos_left]
/--
theorem `mul_le_of_le_one_left'` / 定理 `mul_le_of_le_one_left'`

English:
theorem mul_le_of_le_one_left'
  given: [MulRightMono α] {a b : α} (h : b <= 1)
  proof: calc
    b * a <= 1 * a := mul_le_mul_left h a
    _ = a := one_mul a

@[to_additive]

中文:
定理 mul_le_of_le_one_left'
  条件: [MulRightMono α] {a b : α} (h : b <= 1)
  证明: calc
    b * a <= 1 * a := mul_le_mul_left h a
    _ = a := one_mul a

@[to_additive]

Depends on / 依赖: mul_le_mul_left, one_mul
-/
theorem mul_le_of_le_one_left' [MulRightMono α] {a b : α} (h : b <= 1) :
    b * a <= a :=
  calc
    b * a <= 1 * a := mul_le_mul_left h a
    _ = a := one_mul a

@[to_additive]
/--
theorem `one_le_of_le_mul_right` / 定理 `one_le_of_le_mul_right`

English:
theorem one_le_of_le_mul_right
  given: [MulLeftReflectLE α] {a b : α} (h : a <= a * b)
  proof: le_of_mul_le_mul_left' (a := a) by simpa only [mul_one]

@[to_additive]

中文:
定理 one_le_of_le_mul_right
  条件: [MulLeftReflectLE α] {a b : α} (h : a <= a * b)
  证明: le_of_mul_le_mul_left' (a := a) by simpa only [mul_one]

@[to_additive]

Depends on / 依赖: le_of_mul_le_mul_left, mul_one
-/
theorem one_le_of_le_mul_right [MulLeftReflectLE α] {a b : α} (h : a <= a * b) :
    1 <= b :=
le_of_mul_le_mul_left' (a := a) by simpa only [mul_one]

@[to_additive]
/--
theorem `le_one_of_mul_le_right` / 定理 `le_one_of_mul_le_right`

English:
theorem le_one_of_mul_le_right
  given: [MulLeftReflectLE α] {a b : α} (h : a * b <= a)
  proof: le_of_mul_le_mul_left' (a := a) by simpa only [mul_one]

@[to_additive]

中文:
定理 le_one_of_mul_le_right
  条件: [MulLeftReflectLE α] {a b : α} (h : a * b <= a)
  证明: le_of_mul_le_mul_left' (a := a) by simpa only [mul_one]

@[to_additive]

Depends on / 依赖: le_of_mul_le_mul_left, mul_one
-/
theorem le_one_of_mul_le_right [MulLeftReflectLE α] {a b : α} (h : a * b <= a) :
    b <= 1 :=
le_of_mul_le_mul_left' (a := a) by simpa only [mul_one]

@[to_additive]
/--
theorem `one_le_of_le_mul_left` / 定理 `one_le_of_le_mul_left`

English:
theorem one_le_of_le_mul_left
  statement: [MulRightReflectLE α] {a b : α}
  proof: le_of_mul_le_mul_right' (a := b) by simpa only [one_mul]

@[to_additive]

中文:
定理 one_le_of_le_mul_left
  结论: [MulRightReflectLE α] {a b : α}
  证明: le_of_mul_le_mul_right' (a := b) by simpa only [one_mul]

@[to_additive]

Depends on / 依赖: le_of_mul_le_mul_right, one_mul
-/
theorem one_le_of_le_mul_left [MulRightReflectLE α] {a b : α}
    (h : b <= a * b) :
    1 <= a :=
le_of_mul_le_mul_right' (a := b) by simpa only [one_mul]

@[to_additive]
/--
theorem `le_one_of_mul_le_left` / 定理 `le_one_of_mul_le_left`

English:
theorem le_one_of_mul_le_left
  statement: [MulRightReflectLE α] {a b : α}
  proof: le_of_mul_le_mul_right' (a := b) by simpa only [one_mul]

@[to_additive (attr := simp) le_add_iff_nonneg_right]

中文:
定理 le_one_of_mul_le_left
  结论: [MulRightReflectLE α] {a b : α}
  证明: le_of_mul_le_mul_right' (a := b) by simpa only [one_mul]

@[to_additive (attr := simp) le_add_iff_nonneg_right]

Depends on / 依赖: le_of_mul_le_mul_right, one_mul
-/
theorem le_one_of_mul_le_left [MulRightReflectLE α] {a b : α}
    (h : a * b <= b) :
    a <= 1 :=
le_of_mul_le_mul_right' (a := b) by simpa only [one_mul]

@[to_additive (attr := simp) le_add_iff_nonneg_right]
/--
theorem `le_mul_iff_one_le_right'` / 定理 `le_mul_iff_one_le_right'`

English:
theorem le_mul_iff_one_le_right'
  statement: [MulLeftMono α]
  proof: Iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a)

@[to_additive (attr := simp) le_add_iff_nonneg_left]

中文:
定理 le_mul_iff_one_le_right'
  结论: [MulLeftMono α]
  证明: Iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a)

@[to_additive (attr := simp) le_add_iff_nonneg_left]

Depends on / 依赖: Iff.trans, mul_le_mul_iff_left, mul_one
-/
theorem le_mul_iff_one_le_right' [MulLeftMono α]
    [MulLeftReflectLE α] (a : α) {b : α} :
    a <= a * b ↔ 1 <= b :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a)

@[to_additive (attr := simp) le_add_iff_nonneg_left]
/--
theorem `le_mul_iff_one_le_left'` / 定理 `le_mul_iff_one_le_left'`

English:
theorem le_mul_iff_one_le_left'
  statement: [MulRightMono α]
  proof: Iff.trans (by rw [one_mul]) (mul_le_mul_iff_right a)

@[to_additive (attr := simp) add_le_iff_nonpos_right]

中文:
定理 le_mul_iff_one_le_left'
  结论: [MulRightMono α]
  证明: Iff.trans (by rw [one_mul]) (mul_le_mul_iff_right a)

@[to_additive (attr := simp) add_le_iff_nonpos_right]

Depends on / 依赖: Iff.trans, mul_le_mul_iff_right, one_mul
-/
theorem le_mul_iff_one_le_left' [MulRightMono α]
    [MulRightReflectLE α] (a : α) {b : α} :
    a <= b * a ↔ 1 <= b :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_iff_right a)

@[to_additive (attr := simp) add_le_iff_nonpos_right]
/--
theorem `mul_le_iff_le_one_right'` / 定理 `mul_le_iff_le_one_right'`

English:
theorem mul_le_iff_le_one_right'
  statement: [MulLeftMono α]
  proof: Iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a)

@[to_additive (attr := simp) add_le_iff_nonpos_left]

中文:
定理 mul_le_iff_le_one_right'
  结论: [MulLeftMono α]
  证明: Iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a)

@[to_additive (attr := simp) add_le_iff_nonpos_left]

Depends on / 依赖: Iff.trans, mul_le_mul_iff_left, mul_one
-/
theorem mul_le_iff_le_one_right' [MulLeftMono α]
    [MulLeftReflectLE α] (a : α) {b : α} :
    a * b <= a ↔ b <= 1 :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a)

@[to_additive (attr := simp) add_le_iff_nonpos_left]
/--
theorem `mul_le_iff_le_one_left'` / 定理 `mul_le_iff_le_one_left'`

English:
theorem mul_le_iff_le_one_left'
  statement: [MulRightMono α]
  proof: Iff.trans (by rw [one_mul]) (mul_le_mul_iff_right b)

中文:
定理 mul_le_iff_le_one_left'
  结论: [MulRightMono α]
  证明: Iff.trans (by rw [one_mul]) (mul_le_mul_iff_right b)

Depends on / 依赖: Iff.trans, mul_le_mul_iff_right, one_mul
-/
theorem mul_le_iff_le_one_left' [MulRightMono α]
    [MulRightReflectLE α] {a b : α} :
    a * b <= b ↔ a <= 1 :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_iff_right b)

end LE

section LT

variable [LT α]

@[to_additive lt_add_of_pos_right]
/--
theorem `lt_mul_of_one_lt_right'` / 定理 `lt_mul_of_one_lt_right'`

English:
theorem lt_mul_of_one_lt_right'
  given: [MulLeftStrictMono α] (a : α) {b : α} (h : 1 < b)
  proof: calc
    a = a * 1 := (mul_one a).symm
    _ < a * b := mul_lt_mul_right h a

@[to_additive add_lt_of_neg_right]

中文:
定理 lt_mul_of_one_lt_right'
  条件: [MulLeftStrictMono α] (a : α) {b : α} (h : 1 < b)
  证明: calc
    a = a * 1 := (mul_one a).symm
    _ < a * b := mul_lt_mul_right h a

@[to_additive add_lt_of_neg_right]

Depends on / 依赖: mul_lt_mul_right, mul_one
-/
theorem lt_mul_of_one_lt_right' [MulLeftStrictMono α] (a : α) {b : α} (h : 1 < b) :
    a < a * b :=
  calc
    a = a * 1 := (mul_one a).symm
    _ < a * b := mul_lt_mul_right h a

@[to_additive add_lt_of_neg_right]
/--
theorem `mul_lt_of_lt_one_right'` / 定理 `mul_lt_of_lt_one_right'`

English:
theorem mul_lt_of_lt_one_right'
  given: [MulLeftStrictMono α] (a : α) {b : α} (h : b < 1)
  proof: calc
    a * b < a * 1 := mul_lt_mul_right h a
    _ = a := mul_one a

@[to_additive lt_add_of_pos_left]

中文:
定理 mul_lt_of_lt_one_right'
  条件: [MulLeftStrictMono α] (a : α) {b : α} (h : b < 1)
  证明: calc
    a * b < a * 1 := mul_lt_mul_right h a
    _ = a := mul_one a

@[to_additive lt_add_of_pos_left]

Depends on / 依赖: mul_lt_mul_right, mul_one
-/
theorem mul_lt_of_lt_one_right' [MulLeftStrictMono α] (a : α) {b : α} (h : b < 1) :
    a * b < a :=
  calc
    a * b < a * 1 := mul_lt_mul_right h a
    _ = a := mul_one a

@[to_additive lt_add_of_pos_left]
/--
theorem `lt_mul_of_one_lt_left'` / 定理 `lt_mul_of_one_lt_left'`

English:
theorem lt_mul_of_one_lt_left'
  statement: [MulRightStrictMono α] (a : α) {b : α}
  proof: calc
    a = 1 * a := (one_mul a).symm
    _ < b * a := mul_lt_mul_left h a

@[to_additive add_lt_of_neg_left]

中文:
定理 lt_mul_of_one_lt_left'
  结论: [MulRightStrictMono α] (a : α) {b : α}
  证明: calc
    a = 1 * a := (one_mul a).symm
    _ < b * a := mul_lt_mul_left h a

@[to_additive add_lt_of_neg_left]

Depends on / 依赖: mul_lt_mul_left, one_mul
-/
theorem lt_mul_of_one_lt_left' [MulRightStrictMono α] (a : α) {b : α}
    (h : 1 < b) :
    a < b * a :=
  calc
    a = 1 * a := (one_mul a).symm
    _ < b * a := mul_lt_mul_left h a

@[to_additive add_lt_of_neg_left]
/--
theorem `mul_lt_of_lt_one_left'` / 定理 `mul_lt_of_lt_one_left'`

English:
theorem mul_lt_of_lt_one_left'
  statement: [MulRightStrictMono α] (a : α) {b : α}
  proof: calc
    b * a < 1 * a := mul_lt_mul_left h a
    _ = a := one_mul a

@[to_additive]

中文:
定理 mul_lt_of_lt_one_left'
  结论: [MulRightStrictMono α] (a : α) {b : α}
  证明: calc
    b * a < 1 * a := mul_lt_mul_left h a
    _ = a := one_mul a

@[to_additive]

Depends on / 依赖: mul_lt_mul_left, one_mul
-/
theorem mul_lt_of_lt_one_left' [MulRightStrictMono α] (a : α) {b : α}
    (h : b < 1) :
    b * a < a :=
  calc
    b * a < 1 * a := mul_lt_mul_left h a
    _ = a := one_mul a

@[to_additive]
/--
theorem `one_lt_of_lt_mul_right` / 定理 `one_lt_of_lt_mul_right`

English:
theorem one_lt_of_lt_mul_right
  given: [MulLeftReflectLT α] {a b : α} (h : a < a * b)
  proof: lt_of_mul_lt_mul_left' (a := a) by simpa only [mul_one]

@[to_additive]

中文:
定理 one_lt_of_lt_mul_right
  条件: [MulLeftReflectLT α] {a b : α} (h : a < a * b)
  证明: lt_of_mul_lt_mul_left' (a := a) by simpa only [mul_one]

@[to_additive]

Depends on / 依赖: lt_of_mul_lt_mul_left, mul_one
-/
theorem one_lt_of_lt_mul_right [MulLeftReflectLT α] {a b : α} (h : a < a * b) :
    1 < b :=
lt_of_mul_lt_mul_left' (a := a) by simpa only [mul_one]

@[to_additive]
/--
theorem `lt_one_of_mul_lt_right` / 定理 `lt_one_of_mul_lt_right`

English:
theorem lt_one_of_mul_lt_right
  given: [MulLeftReflectLT α] {a b : α} (h : a * b < a)
  proof: lt_of_mul_lt_mul_left' (a := a) by simpa only [mul_one]

@[to_additive]

中文:
定理 lt_one_of_mul_lt_right
  条件: [MulLeftReflectLT α] {a b : α} (h : a * b < a)
  证明: lt_of_mul_lt_mul_left' (a := a) by simpa only [mul_one]

@[to_additive]

Depends on / 依赖: lt_of_mul_lt_mul_left, mul_one
-/
theorem lt_one_of_mul_lt_right [MulLeftReflectLT α] {a b : α} (h : a * b < a) :
    b < 1 :=
lt_of_mul_lt_mul_left' (a := a) by simpa only [mul_one]

@[to_additive]
/--
theorem `one_lt_of_lt_mul_left` / 定理 `one_lt_of_lt_mul_left`

English:
theorem one_lt_of_lt_mul_left
  statement: [MulRightReflectLT α] {a b : α}
  proof: lt_of_mul_lt_mul_right' (a := b) by simpa only [one_mul]

@[to_additive]

中文:
定理 one_lt_of_lt_mul_left
  结论: [MulRightReflectLT α] {a b : α}
  证明: lt_of_mul_lt_mul_right' (a := b) by simpa only [one_mul]

@[to_additive]

Depends on / 依赖: lt_of_mul_lt_mul_right, one_mul
-/
theorem one_lt_of_lt_mul_left [MulRightReflectLT α] {a b : α}
    (h : b < a * b) :
    1 < a :=
lt_of_mul_lt_mul_right' (a := b) by simpa only [one_mul]

@[to_additive]
/--
theorem `lt_one_of_mul_lt_left` / 定理 `lt_one_of_mul_lt_left`

English:
theorem lt_one_of_mul_lt_left
  statement: [MulRightReflectLT α] {a b : α}
  proof: lt_of_mul_lt_mul_right' (a := b) by simpa only [one_mul]

@[to_additive (attr := simp) lt_add_iff_pos_right]

中文:
定理 lt_one_of_mul_lt_left
  结论: [MulRightReflectLT α] {a b : α}
  证明: lt_of_mul_lt_mul_right' (a := b) by simpa only [one_mul]

@[to_additive (attr := simp) lt_add_iff_pos_right]

Depends on / 依赖: lt_of_mul_lt_mul_right, one_mul
-/
theorem lt_one_of_mul_lt_left [MulRightReflectLT α] {a b : α}
    (h : a * b < b) :
    a < 1 :=
lt_of_mul_lt_mul_right' (a := b) by simpa only [one_mul]

@[to_additive (attr := simp) lt_add_iff_pos_right]
/--
theorem `lt_mul_iff_one_lt_right'` / 定理 `lt_mul_iff_one_lt_right'`

English:
theorem lt_mul_iff_one_lt_right'
  statement: [MulLeftStrictMono α]
  proof: Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_left a)

@[to_additive (attr := simp) lt_add_iff_pos_left]

中文:
定理 lt_mul_iff_one_lt_right'
  结论: [MulLeftStrictMono α]
  证明: Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_left a)

@[to_additive (attr := simp) lt_add_iff_pos_left]

Depends on / 依赖: Iff.trans, mul_lt_mul_iff_left, mul_one
-/
theorem lt_mul_iff_one_lt_right' [MulLeftStrictMono α]
    [MulLeftReflectLT α] (a : α) {b : α} :
    a < a * b ↔ 1 < b :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_left a)

@[to_additive (attr := simp) lt_add_iff_pos_left]
/--
theorem `lt_mul_iff_one_lt_left'` / 定理 `lt_mul_iff_one_lt_left'`

English:
theorem lt_mul_iff_one_lt_left'
  statement: [MulRightStrictMono α]
  proof: Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_right a)

@[to_additive (attr := simp) add_lt_iff_neg_left]

中文:
定理 lt_mul_iff_one_lt_left'
  结论: [MulRightStrictMono α]
  证明: Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_right a)

@[to_additive (attr := simp) add_lt_iff_neg_left]

Depends on / 依赖: Iff.trans, mul_lt_mul_iff_right, one_mul
-/
theorem lt_mul_iff_one_lt_left' [MulRightStrictMono α]
    [MulRightReflectLT α] (a : α) {b : α} : a < b * a ↔ 1 < b :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_right a)

@[to_additive (attr := simp) add_lt_iff_neg_left]
/--
theorem `mul_lt_iff_lt_one_left'` / 定理 `mul_lt_iff_lt_one_left'`

English:
theorem mul_lt_iff_lt_one_left'
  statement: [MulLeftStrictMono α]
  proof: Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_left a)

@[to_additive (attr := simp) add_lt_iff_neg_right]

中文:
定理 mul_lt_iff_lt_one_left'
  结论: [MulLeftStrictMono α]
  证明: Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_left a)

@[to_additive (attr := simp) add_lt_iff_neg_right]

Depends on / 依赖: Iff.trans, mul_lt_mul_iff_left, mul_one
-/
theorem mul_lt_iff_lt_one_left' [MulLeftStrictMono α]
    [MulLeftReflectLT α] {a b : α} :
    a * b < a ↔ b < 1 :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_left a)

@[to_additive (attr := simp) add_lt_iff_neg_right]
/--
theorem `mul_lt_iff_lt_one_right'` / 定理 `mul_lt_iff_lt_one_right'`

English:
theorem mul_lt_iff_lt_one_right'
  statement: [MulRightStrictMono α]
  proof: Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_right b)

中文:
定理 mul_lt_iff_lt_one_right'
  结论: [MulRightStrictMono α]
  证明: Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_right b)

Depends on / 依赖: Iff.trans, mul_lt_mul_iff_right, one_mul
-/
theorem mul_lt_iff_lt_one_right' [MulRightStrictMono α]
    [MulRightReflectLT α] {a : α} (b : α) : a * b < b ↔ a < 1 :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_right b)

end LT

section Preorder

variable [Preorder α]

/-! Lemmas of the form `b ≤ c → a ≤ 1 → b * a ≤ c`,
which assume left covariance. -/


@[to_additive]
/--
theorem `mul_le_of_le_of_le_one` / 定理 `mul_le_of_le_of_le_one`

English:
theorem mul_le_of_le_of_le_one
  statement: [MulLeftMono α] {a b c : α} (hbc : b <= c)
  proof: calc
    b * a <= b * 1 := mul_le_mul_right ha b
    _ = b := mul_one b
    _ <= c := hbc

@[to_additive]

中文:
定理 mul_le_of_le_of_le_one
  结论: [MulLeftMono α] {a b c : α} (hbc : b <= c)
  证明: calc
    b * a <= b * 1 := mul_le_mul_right ha b
    _ = b := mul_one b
    _ <= c := hbc

@[to_additive]

Depends on / 依赖: mul_le_mul_right, mul_one
-/
theorem mul_le_of_le_of_le_one [MulLeftMono α] {a b c : α} (hbc : b <= c)
    (ha : a <= 1) :
    b * a <= c :=
  calc
    b * a <= b * 1 := mul_le_mul_right ha b
    _ = b := mul_one b
    _ <= c := hbc

@[to_additive]
/--
theorem `mul_lt_of_le_of_lt_one` / 定理 `mul_lt_of_le_of_lt_one`

English:
theorem mul_lt_of_le_of_lt_one
  statement: [MulLeftStrictMono α] {a b c : α} (hbc : b <= c)
  proof: calc
    b * a < b * 1 := mul_lt_mul_right ha b
    _ = b := mul_one b
    _ <= c := hbc

@[to_additive]

中文:
定理 mul_lt_of_le_of_lt_one
  结论: [MulLeftStrictMono α] {a b c : α} (hbc : b <= c)
  证明: calc
    b * a < b * 1 := mul_lt_mul_right ha b
    _ = b := mul_one b
    _ <= c := hbc

@[to_additive]

Depends on / 依赖: mul_lt_mul_right, mul_one
-/
theorem mul_lt_of_le_of_lt_one [MulLeftStrictMono α] {a b c : α} (hbc : b <= c)
    (ha : a < 1) :
    b * a < c :=
  calc
    b * a < b * 1 := mul_lt_mul_right ha b
    _ = b := mul_one b
    _ <= c := hbc

@[to_additive]
/--
theorem `mul_lt_of_lt_of_le_one` / 定理 `mul_lt_of_lt_of_le_one`

English:
theorem mul_lt_of_lt_of_le_one
  statement: [MulLeftMono α] {a b c : α} (hbc : b < c)
  proof: calc
    b * a <= b * 1 := mul_le_mul_right ha b
    _ = b := mul_one b
    _ < c := hbc

@[to_additive]

中文:
定理 mul_lt_of_lt_of_le_one
  结论: [MulLeftMono α] {a b c : α} (hbc : b < c)
  证明: calc
    b * a <= b * 1 := mul_le_mul_right ha b
    _ = b := mul_one b
    _ < c := hbc

@[to_additive]

Depends on / 依赖: mul_le_mul_right, mul_one
-/
theorem mul_lt_of_lt_of_le_one [MulLeftMono α] {a b c : α} (hbc : b < c)
    (ha : a <= 1) :
    b * a < c :=
  calc
    b * a <= b * 1 := mul_le_mul_right ha b
    _ = b := mul_one b
    _ < c := hbc

@[to_additive]
/--
theorem `mul_lt_of_lt_of_lt_one` / 定理 `mul_lt_of_lt_of_lt_one`

English:
theorem mul_lt_of_lt_of_lt_one
  statement: [MulLeftStrictMono α] {a b c : α} (hbc : b < c)
  proof: calc
    b * a < b * 1 := mul_lt_mul_right ha b
    _ = b := mul_one b
    _ < c := hbc

@[to_additive]

中文:
定理 mul_lt_of_lt_of_lt_one
  结论: [MulLeftStrictMono α] {a b c : α} (hbc : b < c)
  证明: calc
    b * a < b * 1 := mul_lt_mul_right ha b
    _ = b := mul_one b
    _ < c := hbc

@[to_additive]

Depends on / 依赖: mul_lt_mul_right, mul_one
-/
theorem mul_lt_of_lt_of_lt_one [MulLeftStrictMono α] {a b c : α} (hbc : b < c)
    (ha : a < 1) :
    b * a < c :=
  calc
    b * a < b * 1 := mul_lt_mul_right ha b
    _ = b := mul_one b
    _ < c := hbc

@[to_additive]
/--
theorem `mul_lt_of_lt_of_lt_one'` / 定理 `mul_lt_of_lt_of_lt_one'`

English:
theorem mul_lt_of_lt_of_lt_one'
  statement: [MulLeftMono α] {a b c : α} (hbc : b < c)
  proof: mul_lt_of_lt_of_le_one hbc ha.le

中文:
定理 mul_lt_of_lt_of_lt_one'
  结论: [MulLeftMono α] {a b c : α} (hbc : b < c)
  证明: mul_lt_of_lt_of_le_one hbc ha.le

Depends on / 依赖: ha.le, mul_lt_of_lt_of_le_one
-/
theorem mul_lt_of_lt_of_lt_one' [MulLeftMono α] {a b c : α} (hbc : b < c)
    (ha : a < 1) :
    b * a < c :=
  mul_lt_of_lt_of_le_one hbc ha.le

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.mul_le_one`. -/
@[to_additive /-- Assumes left covariance.
The lemma assuming right covariance is `Right.add_nonpos`. -/]
/--
theorem `Left.mul_le_one` / 定理 `Left.mul_le_one`

English:
theorem Left.mul_le_one
  given: [MulLeftMono α] {a b : α} (ha : a <= 1) (hb : b <= 1)
  proof: mul_le_of_le_of_le_one ha hb

中文:
定理 Left.mul_le_one
  条件: [MulLeftMono α] {a b : α} (ha : a <= 1) (hb : b <= 1)
  证明: mul_le_of_le_of_le_one ha hb

Depends on / 依赖: mul_le_of_le_of_le_one
-/
theorem Left.mul_le_one [MulLeftMono α] {a b : α} (ha : a <= 1) (hb : b <= 1) :
    a * b <= 1 :=
  mul_le_of_le_of_le_one ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.mul_lt_one_of_le_of_lt`. -/
@[to_additive Left.add_neg_of_nonpos_of_neg
      /-- Assumes left covariance.
      The lemma assuming right covariance is `Right.add_neg_of_nonpos_of_neg`. -/]
/--
theorem `Left.mul_lt_one_of_le_of_lt` / 定理 `Left.mul_lt_one_of_le_of_lt`

English:
theorem Left.mul_lt_one_of_le_of_lt
  statement: [MulLeftStrictMono α] {a b : α} (ha : a <= 1)
  proof: mul_lt_of_le_of_lt_one ha hb

中文:
定理 Left.mul_lt_one_of_le_of_lt
  结论: [MulLeftStrictMono α] {a b : α} (ha : a <= 1)
  证明: mul_lt_of_le_of_lt_one ha hb

Depends on / 依赖: mul_lt_of_le_of_lt_one
-/
theorem Left.mul_lt_one_of_le_of_lt [MulLeftStrictMono α] {a b : α} (ha : a <= 1)
    (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_le_of_lt_one ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.mul_lt_one_of_lt_of_le`. -/
@[to_additive Left.add_neg_of_neg_of_nonpos
      /-- Assumes left covariance.
      The lemma assuming right covariance is `Right.add_neg_of_neg_of_nonpos`. -/]
/--
theorem `Left.mul_lt_one_of_lt_of_le` / 定理 `Left.mul_lt_one_of_lt_of_le`

English:
theorem Left.mul_lt_one_of_lt_of_le
  statement: [MulLeftMono α] {a b : α} (ha : a < 1)
  proof: mul_lt_of_lt_of_le_one ha hb

中文:
定理 Left.mul_lt_one_of_lt_of_le
  结论: [MulLeftMono α] {a b : α} (ha : a < 1)
  证明: mul_lt_of_lt_of_le_one ha hb

Depends on / 依赖: mul_lt_of_lt_of_le_one
-/
theorem Left.mul_lt_one_of_lt_of_le [MulLeftMono α] {a b : α} (ha : a < 1)
    (hb : b <= 1) :
    a * b < 1 :=
  mul_lt_of_lt_of_le_one ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.mul_lt_one`. -/
@[to_additive /-- Assumes left covariance.
The lemma assuming right covariance is `Right.add_neg`. -/]
/--
theorem `Left.mul_lt_one` / 定理 `Left.mul_lt_one`

English:
theorem Left.mul_lt_one
  given: [MulLeftStrictMono α] {a b : α} (ha : a < 1) (hb : b < 1)
  proof: mul_lt_of_lt_of_lt_one ha hb

中文:
定理 Left.mul_lt_one
  条件: [MulLeftStrictMono α] {a b : α} (ha : a < 1) (hb : b < 1)
  证明: mul_lt_of_lt_of_lt_one ha hb

Depends on / 依赖: mul_lt_of_lt_of_lt_one
-/
theorem Left.mul_lt_one [MulLeftStrictMono α] {a b : α} (ha : a < 1) (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_lt_of_lt_one ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.mul_lt_one'`. -/
@[to_additive /-- Assumes left covariance.
The lemma assuming right covariance is `Right.add_neg'`. -/]
/--
theorem `Left.mul_lt_one'` / 定理 `Left.mul_lt_one'`

English:
theorem Left.mul_lt_one'
  given: [MulLeftMono α] {a b : α} (ha : a < 1) (hb : b < 1)
  proof: mul_lt_of_lt_of_lt_one' ha hb

中文:
定理 Left.mul_lt_one'
  条件: [MulLeftMono α] {a b : α} (ha : a < 1) (hb : b < 1)
  证明: mul_lt_of_lt_of_lt_one' ha hb

Depends on / 依赖: mul_lt_of_lt_of_lt_one
-/
theorem Left.mul_lt_one' [MulLeftMono α] {a b : α} (ha : a < 1) (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_lt_of_lt_one' ha hb

/-! Lemmas of the form `b ≤ c → 1 ≤ a → b ≤ c * a`,
which assume left covariance. -/


@[to_additive]
/--
theorem `le_mul_of_le_of_one_le` / 定理 `le_mul_of_le_of_one_le`

English:
theorem le_mul_of_le_of_one_le
  statement: [MulLeftMono α] {a b c : α} (hbc : b <= c)
  proof: calc
    b <= c := hbc
    _ = c * 1 := (mul_one c).symm
    _ <= c * a := mul_le_mul_right ha c

@[to_additive]

中文:
定理 le_mul_of_le_of_one_le
  结论: [MulLeftMono α] {a b c : α} (hbc : b <= c)
  证明: calc
    b <= c := hbc
    _ = c * 1 := (mul_one c).symm
    _ <= c * a := mul_le_mul_right ha c

@[to_additive]

Depends on / 依赖: mul_le_mul_right, mul_one
-/
theorem le_mul_of_le_of_one_le [MulLeftMono α] {a b c : α} (hbc : b <= c)
    (ha : 1 <= a) :
    b <= c * a :=
  calc
    b <= c := hbc
    _ = c * 1 := (mul_one c).symm
    _ <= c * a := mul_le_mul_right ha c

@[to_additive]
/--
theorem `lt_mul_of_le_of_one_lt` / 定理 `lt_mul_of_le_of_one_lt`

English:
theorem lt_mul_of_le_of_one_lt
  statement: [MulLeftStrictMono α] {a b c : α} (hbc : b <= c)
  proof: calc
    b <= c := hbc
    _ = c * 1 := (mul_one c).symm
    _ < c * a := mul_lt_mul_right ha c

@[to_additive]

中文:
定理 lt_mul_of_le_of_one_lt
  结论: [MulLeftStrictMono α] {a b c : α} (hbc : b <= c)
  证明: calc
    b <= c := hbc
    _ = c * 1 := (mul_one c).symm
    _ < c * a := mul_lt_mul_right ha c

@[to_additive]

Depends on / 依赖: mul_lt_mul_right, mul_one
-/
theorem lt_mul_of_le_of_one_lt [MulLeftStrictMono α] {a b c : α} (hbc : b <= c)
    (ha : 1 < a) :
    b < c * a :=
  calc
    b <= c := hbc
    _ = c * 1 := (mul_one c).symm
    _ < c * a := mul_lt_mul_right ha c

@[to_additive]
/--
theorem `lt_mul_of_lt_of_one_le` / 定理 `lt_mul_of_lt_of_one_le`

English:
theorem lt_mul_of_lt_of_one_le
  statement: [MulLeftMono α] {a b c : α} (hbc : b < c)
  proof: calc
    b < c := hbc
    _ = c * 1 := (mul_one c).symm
    _ <= c * a := mul_le_mul_right ha c

@[to_additive]

中文:
定理 lt_mul_of_lt_of_one_le
  结论: [MulLeftMono α] {a b c : α} (hbc : b < c)
  证明: calc
    b < c := hbc
    _ = c * 1 := (mul_one c).symm
    _ <= c * a := mul_le_mul_right ha c

@[to_additive]

Depends on / 依赖: mul_le_mul_right, mul_one
-/
theorem lt_mul_of_lt_of_one_le [MulLeftMono α] {a b c : α} (hbc : b < c)
    (ha : 1 <= a) :
    b < c * a :=
  calc
    b < c := hbc
    _ = c * 1 := (mul_one c).symm
    _ <= c * a := mul_le_mul_right ha c

@[to_additive]
/--
theorem `lt_mul_of_lt_of_one_lt` / 定理 `lt_mul_of_lt_of_one_lt`

English:
theorem lt_mul_of_lt_of_one_lt
  statement: [MulLeftStrictMono α] {a b c : α} (hbc : b < c)
  proof: calc
    b < c := hbc
    _ = c * 1 := (mul_one c).symm
    _ < c * a := mul_lt_mul_right ha c

@[to_additive]

中文:
定理 lt_mul_of_lt_of_one_lt
  结论: [MulLeftStrictMono α] {a b c : α} (hbc : b < c)
  证明: calc
    b < c := hbc
    _ = c * 1 := (mul_one c).symm
    _ < c * a := mul_lt_mul_right ha c

@[to_additive]

Depends on / 依赖: mul_lt_mul_right, mul_one
-/
theorem lt_mul_of_lt_of_one_lt [MulLeftStrictMono α] {a b c : α} (hbc : b < c)
    (ha : 1 < a) :
    b < c * a :=
  calc
    b < c := hbc
    _ = c * 1 := (mul_one c).symm
    _ < c * a := mul_lt_mul_right ha c

@[to_additive]
/--
theorem `lt_mul_of_lt_of_one_lt'` / 定理 `lt_mul_of_lt_of_one_lt'`

English:
theorem lt_mul_of_lt_of_one_lt'
  statement: [MulLeftMono α] {a b c : α} (hbc : b < c)
  proof: lt_mul_of_lt_of_one_le hbc ha.le

中文:
定理 lt_mul_of_lt_of_one_lt'
  结论: [MulLeftMono α] {a b c : α} (hbc : b < c)
  证明: lt_mul_of_lt_of_one_le hbc ha.le

Depends on / 依赖: ha.le, lt_mul_of_lt_of_one_le
-/
theorem lt_mul_of_lt_of_one_lt' [MulLeftMono α] {a b c : α} (hbc : b < c)
    (ha : 1 < a) :
    b < c * a :=
  lt_mul_of_lt_of_one_le hbc ha.le

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.one_le_mul`. -/
@[to_additive Left.add_nonneg /-- Assumes left covariance.
The lemma assuming right covariance is `Right.add_nonneg`. -/]
/--
theorem `Left.one_le_mul` / 定理 `Left.one_le_mul`

English:
theorem Left.one_le_mul
  given: [MulLeftMono α] {a b : α} (ha : 1 <= a) (hb : 1 <= b)
  proof: le_mul_of_le_of_one_le ha hb

中文:
定理 Left.one_le_mul
  条件: [MulLeftMono α] {a b : α} (ha : 1 <= a) (hb : 1 <= b)
  证明: le_mul_of_le_of_one_le ha hb

Depends on / 依赖: le_mul_of_le_of_one_le
-/
theorem Left.one_le_mul [MulLeftMono α] {a b : α} (ha : 1 <= a) (hb : 1 <= b) :
    1 <= a * b :=
  le_mul_of_le_of_one_le ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.one_lt_mul_of_le_of_lt`. -/
@[to_additive Left.add_pos_of_nonneg_of_pos
      /-- Assumes left covariance.
      The lemma assuming right covariance is `Right.add_pos_of_nonneg_of_pos`. -/]
/--
theorem `Left.one_lt_mul_of_le_of_lt` / 定理 `Left.one_lt_mul_of_le_of_lt`

English:
theorem Left.one_lt_mul_of_le_of_lt
  statement: [MulLeftStrictMono α] {a b : α} (ha : 1 <= a)
  proof: lt_mul_of_le_of_one_lt ha hb

@[to_additive]

中文:
定理 Left.one_lt_mul_of_le_of_lt
  结论: [MulLeftStrictMono α] {a b : α} (ha : 1 <= a)
  证明: lt_mul_of_le_of_one_lt ha hb

@[to_additive]

Depends on / 依赖: lt_mul_of_le_of_one_lt
-/
theorem Left.one_lt_mul_of_le_of_lt [MulLeftStrictMono α] {a b : α} (ha : 1 <= a)
    (hb : 1 < b) :
    1 < a * b :=
  lt_mul_of_le_of_one_lt ha hb

@[to_additive]
/--
theorem `Left.one_lt_mul_of_right` / 定理 `Left.one_lt_mul_of_right`

English:
theorem Left.one_lt_mul_of_right
  statement: [IsBotOneClass α] [MulLeftStrictMono α] {b : α}
  proof: Left.one_lt_mul_of_le_of_lt one_le hb

中文:
定理 Left.one_lt_mul_of_right
  结论: [是BotOne类 α] [MulLeftStrictMono α] {b : α}
  证明: Left.one_lt_mul_of_le_of_lt one_le hb

Depends on / 依赖: Left.one_lt_mul_of_le_of_lt, one_le, one_lt_mul_of_le_of_lt
-/
theorem Left.one_lt_mul_of_right [IsBotOneClass α] [MulLeftStrictMono α] {b : α}
    (hb : 1 < b) (a : α) : 1 < a * b :=
  Left.one_lt_mul_of_le_of_lt one_le hb

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.one_lt_mul_of_lt_of_le`. -/
@[to_additive Left.add_pos_of_pos_of_nonneg
      /-- Assumes left covariance.
      The lemma assuming right covariance is `Right.add_pos_of_pos_of_nonneg`. -/]
/--
theorem `Left.one_lt_mul_of_lt_of_le` / 定理 `Left.one_lt_mul_of_lt_of_le`

English:
theorem Left.one_lt_mul_of_lt_of_le
  statement: [MulLeftMono α] {a b : α} (ha : 1 < a)
  proof: lt_mul_of_lt_of_one_le ha hb

@[to_additive]

中文:
定理 Left.one_lt_mul_of_lt_of_le
  结论: [MulLeftMono α] {a b : α} (ha : 1 < a)
  证明: lt_mul_of_lt_of_one_le ha hb

@[to_additive]

Depends on / 依赖: lt_mul_of_lt_of_one_le
-/
theorem Left.one_lt_mul_of_lt_of_le [MulLeftMono α] {a b : α} (ha : 1 < a)
    (hb : 1 <= b) :
    1 < a * b :=
  lt_mul_of_lt_of_one_le ha hb

@[to_additive]
/--
theorem `Left.one_lt_mul_of_left` / 定理 `Left.one_lt_mul_of_left`

English:
theorem Left.one_lt_mul_of_left
  statement: [IsBotOneClass α] [MulLeftMono α] {a : α}
  proof: Left.one_lt_mul_of_lt_of_le ha one_le

@[to_additive add_pos_of_left] alias one_lt_mul_of_left := Left.one_lt_mul_of_left

中文:
定理 Left.one_lt_mul_of_left
  结论: [是BotOne类 α] [MulLeftMono α] {a : α}
  证明: Left.one_lt_mul_of_lt_of_le ha one_le

@[to_additive add_pos_of_left] alias one_lt_mul_of_left := Left.one_lt_mul_of_left

Depends on / 依赖: Left.one_lt_mul_of_lt_of_le, one_le, one_lt_mul_of_lt_of_le
-/
theorem Left.one_lt_mul_of_left [IsBotOneClass α] [MulLeftMono α] {a : α}
    (ha : 1 < a) (b : α) : 1 < a * b :=
  Left.one_lt_mul_of_lt_of_le ha one_le

@[to_additive add_pos_of_left] alias one_lt_mul_of_left := Left.one_lt_mul_of_left

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.one_lt_mul`. -/
@[to_additive Left.add_pos /-- Assumes left covariance.
The lemma assuming right covariance is `Right.add_pos`. -/]
/--
theorem `Left.one_lt_mul` / 定理 `Left.one_lt_mul`

English:
theorem Left.one_lt_mul
  given: [MulLeftStrictMono α] {a b : α} (ha : 1 < a) (hb : 1 < b)
  proof: lt_mul_of_lt_of_one_lt ha hb

中文:
定理 Left.one_lt_mul
  条件: [MulLeftStrictMono α] {a b : α} (ha : 1 < a) (hb : 1 < b)
  证明: lt_mul_of_lt_of_one_lt ha hb

Depends on / 依赖: lt_mul_of_lt_of_one_lt
-/
theorem Left.one_lt_mul [MulLeftStrictMono α] {a b : α} (ha : 1 < a) (hb : 1 < b) :
    1 < a * b :=
  lt_mul_of_lt_of_one_lt ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.one_lt_mul'`. -/
@[to_additive Left.add_pos' /-- Assumes left covariance.
The lemma assuming right covariance is `Right.add_pos'`. -/]
/--
theorem `Left.one_lt_mul'` / 定理 `Left.one_lt_mul'`

English:
theorem Left.one_lt_mul'
  given: [MulLeftMono α] {a b : α} (ha : 1 < a) (hb : 1 < b)
  proof: lt_mul_of_lt_of_one_lt' ha hb

中文:
定理 Left.one_lt_mul'
  条件: [MulLeftMono α] {a b : α} (ha : 1 < a) (hb : 1 < b)
  证明: lt_mul_of_lt_of_one_lt' ha hb

Depends on / 依赖: lt_mul_of_lt_of_one_lt
-/
theorem Left.one_lt_mul' [MulLeftMono α] {a b : α} (ha : 1 < a) (hb : 1 < b) :
    1 < a * b :=
  lt_mul_of_lt_of_one_lt' ha hb

/-! Lemmas of the form `a ≤ 1 → b ≤ c → a * b ≤ c`,
which assume right covariance. -/


@[to_additive]
/--
theorem `mul_le_of_le_one_of_le` / 定理 `mul_le_of_le_one_of_le`

English:
theorem mul_le_of_le_one_of_le
  statement: [MulRightMono α] {a b c : α} (ha : a <= 1)
  proof: calc
    a * b <= 1 * b := mul_le_mul_left ha b
    _ = b := one_mul b
    _ <= c := hbc

@[to_additive]

中文:
定理 mul_le_of_le_one_of_le
  结论: [MulRightMono α] {a b c : α} (ha : a <= 1)
  证明: calc
    a * b <= 1 * b := mul_le_mul_left ha b
    _ = b := one_mul b
    _ <= c := hbc

@[to_additive]

Depends on / 依赖: mul_le_mul_left, one_mul
-/
theorem mul_le_of_le_one_of_le [MulRightMono α] {a b c : α} (ha : a <= 1)
    (hbc : b <= c) :
    a * b <= c :=
  calc
    a * b <= 1 * b := mul_le_mul_left ha b
    _ = b := one_mul b
    _ <= c := hbc

@[to_additive]
/--
theorem `mul_lt_of_lt_one_of_le` / 定理 `mul_lt_of_lt_one_of_le`

English:
theorem mul_lt_of_lt_one_of_le
  statement: [MulRightStrictMono α] {a b c : α} (ha : a < 1)
  proof: calc
    a * b < 1 * b := mul_lt_mul_left ha b
    _ = b := one_mul b
    _ <= c := hbc

@[to_additive]

中文:
定理 mul_lt_of_lt_one_of_le
  结论: [MulRightStrictMono α] {a b c : α} (ha : a < 1)
  证明: calc
    a * b < 1 * b := mul_lt_mul_left ha b
    _ = b := one_mul b
    _ <= c := hbc

@[to_additive]

Depends on / 依赖: mul_lt_mul_left, one_mul
-/
theorem mul_lt_of_lt_one_of_le [MulRightStrictMono α] {a b c : α} (ha : a < 1)
    (hbc : b <= c) :
    a * b < c :=
  calc
    a * b < 1 * b := mul_lt_mul_left ha b
    _ = b := one_mul b
    _ <= c := hbc

@[to_additive]
/--
theorem `mul_lt_of_le_one_of_lt` / 定理 `mul_lt_of_le_one_of_lt`

English:
theorem mul_lt_of_le_one_of_lt
  statement: [MulRightMono α] {a b c : α} (ha : a <= 1)
  proof: calc
    a * b <= 1 * b := mul_le_mul_left ha b
    _ = b := one_mul b
    _ < c := hb

@[to_additive]

中文:
定理 mul_lt_of_le_one_of_lt
  结论: [MulRightMono α] {a b c : α} (ha : a <= 1)
  证明: calc
    a * b <= 1 * b := mul_le_mul_left ha b
    _ = b := one_mul b
    _ < c := hb

@[to_additive]

Depends on / 依赖: mul_le_mul_left, one_mul
-/
theorem mul_lt_of_le_one_of_lt [MulRightMono α] {a b c : α} (ha : a <= 1)
    (hb : b < c) :
    a * b < c :=
  calc
    a * b <= 1 * b := mul_le_mul_left ha b
    _ = b := one_mul b
    _ < c := hb

@[to_additive]
/--
theorem `mul_lt_of_lt_one_of_lt` / 定理 `mul_lt_of_lt_one_of_lt`

English:
theorem mul_lt_of_lt_one_of_lt
  statement: [MulRightStrictMono α] {a b c : α} (ha : a < 1)
  proof: calc
    a * b < 1 * b := mul_lt_mul_left ha b
    _ = b := one_mul b
    _ < c := hb

@[to_additive]

中文:
定理 mul_lt_of_lt_one_of_lt
  结论: [MulRightStrictMono α] {a b c : α} (ha : a < 1)
  证明: calc
    a * b < 1 * b := mul_lt_mul_left ha b
    _ = b := one_mul b
    _ < c := hb

@[to_additive]

Depends on / 依赖: mul_lt_mul_left, one_mul
-/
theorem mul_lt_of_lt_one_of_lt [MulRightStrictMono α] {a b c : α} (ha : a < 1)
    (hb : b < c) :
    a * b < c :=
  calc
    a * b < 1 * b := mul_lt_mul_left ha b
    _ = b := one_mul b
    _ < c := hb

@[to_additive]
/--
theorem `mul_lt_of_lt_one_of_lt'` / 定理 `mul_lt_of_lt_one_of_lt'`

English:
theorem mul_lt_of_lt_one_of_lt'
  statement: [MulRightMono α] {a b c : α} (ha : a < 1)
  proof: mul_lt_of_le_one_of_lt ha.le hbc

中文:
定理 mul_lt_of_lt_one_of_lt'
  结论: [MulRightMono α] {a b c : α} (ha : a < 1)
  证明: mul_lt_of_le_one_of_lt ha.le hbc

Depends on / 依赖: ha.le, mul_lt_of_le_one_of_lt
-/
theorem mul_lt_of_lt_one_of_lt' [MulRightMono α] {a b c : α} (ha : a < 1)
    (hbc : b < c) :
    a * b < c :=
  mul_lt_of_le_one_of_lt ha.le hbc

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.mul_le_one`. -/
@[to_additive /-- Assumes right covariance.
The lemma assuming left covariance is `Left.add_nonpos`. -/]
/--
theorem `Right.mul_le_one` / 定理 `Right.mul_le_one`

English:
theorem Right.mul_le_one
  statement: [MulRightMono α] {a b : α} (ha : a <= 1)
  proof: mul_le_of_le_one_of_le ha hb

中文:
定理 Right.mul_le_one
  结论: [MulRightMono α] {a b : α} (ha : a <= 1)
  证明: mul_le_of_le_one_of_le ha hb

Depends on / 依赖: mul_le_of_le_one_of_le
-/
theorem Right.mul_le_one [MulRightMono α] {a b : α} (ha : a <= 1)
    (hb : b <= 1) :
    a * b <= 1 :=
  mul_le_of_le_one_of_le ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.mul_lt_one_of_lt_of_le`. -/
@[to_additive Right.add_neg_of_neg_of_nonpos
      /-- Assumes right covariance.
      The lemma assuming left covariance is `Left.add_neg_of_neg_of_nonpos`. -/]
/--
theorem `Right.mul_lt_one_of_lt_of_le` / 定理 `Right.mul_lt_one_of_lt_of_le`

English:
theorem Right.mul_lt_one_of_lt_of_le
  statement: [MulRightStrictMono α] {a b : α}
  proof: mul_lt_of_lt_one_of_le ha hb

中文:
定理 Right.mul_lt_one_of_lt_of_le
  结论: [MulRightStrictMono α] {a b : α}
  证明: mul_lt_of_lt_one_of_le ha hb

Depends on / 依赖: mul_lt_of_lt_one_of_le
-/
theorem Right.mul_lt_one_of_lt_of_le [MulRightStrictMono α] {a b : α}
    (ha : a < 1) (hb : b <= 1) :
    a * b < 1 :=
  mul_lt_of_lt_one_of_le ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.mul_lt_one_of_le_of_lt`. -/
@[to_additive Right.add_neg_of_nonpos_of_neg
      /-- Assumes right covariance.
      The lemma assuming left covariance is `Left.add_neg_of_nonpos_of_neg`. -/]
/--
theorem `Right.mul_lt_one_of_le_of_lt` / 定理 `Right.mul_lt_one_of_le_of_lt`

English:
theorem Right.mul_lt_one_of_le_of_lt
  statement: [MulRightMono α] {a b : α}
  proof: mul_lt_of_le_one_of_lt ha hb

中文:
定理 Right.mul_lt_one_of_le_of_lt
  结论: [MulRightMono α] {a b : α}
  证明: mul_lt_of_le_one_of_lt ha hb

Depends on / 依赖: mul_lt_of_le_one_of_lt
-/
theorem Right.mul_lt_one_of_le_of_lt [MulRightMono α] {a b : α}
    (ha : a <= 1) (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_le_one_of_lt ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.mul_lt_one`. -/
@[to_additive /-- Assumes right covariance.
The lemma assuming left covariance is `Left.add_neg`. -/]
/--
theorem `Right.mul_lt_one` / 定理 `Right.mul_lt_one`

English:
theorem Right.mul_lt_one
  statement: [MulRightStrictMono α] {a b : α} (ha : a < 1)
  proof: mul_lt_of_lt_one_of_lt ha hb

中文:
定理 Right.mul_lt_one
  结论: [MulRightStrictMono α] {a b : α} (ha : a < 1)
  证明: mul_lt_of_lt_one_of_lt ha hb

Depends on / 依赖: mul_lt_of_lt_one_of_lt
-/
theorem Right.mul_lt_one [MulRightStrictMono α] {a b : α} (ha : a < 1)
    (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_lt_one_of_lt ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.mul_lt_one'`. -/
@[to_additive /-- Assumes right covariance.
The lemma assuming left covariance is `Left.add_neg'`. -/]
/--
theorem `Right.mul_lt_one'` / 定理 `Right.mul_lt_one'`

English:
theorem Right.mul_lt_one'
  statement: [MulRightMono α] {a b : α} (ha : a < 1)
  proof: mul_lt_of_lt_one_of_lt' ha hb

中文:
定理 Right.mul_lt_one'
  结论: [MulRightMono α] {a b : α} (ha : a < 1)
  证明: mul_lt_of_lt_one_of_lt' ha hb

Depends on / 依赖: mul_lt_of_lt_one_of_lt
-/
theorem Right.mul_lt_one' [MulRightMono α] {a b : α} (ha : a < 1)
    (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_lt_one_of_lt' ha hb

/-! Lemmas of the form `1 ≤ a → b ≤ c → b ≤ a * c`,
which assume right covariance. -/


@[to_additive]
/--
theorem `le_mul_of_one_le_of_le` / 定理 `le_mul_of_one_le_of_le`

English:
theorem le_mul_of_one_le_of_le
  statement: [MulRightMono α] {a b c : α} (ha : 1 <= a)
  proof: calc
    b <= c := hbc
    _ = 1 * c := (one_mul c).symm
    _ <= a * c := mul_le_mul_left ha c

@[to_additive]

中文:
定理 le_mul_of_one_le_of_le
  结论: [MulRightMono α] {a b c : α} (ha : 1 <= a)
  证明: calc
    b <= c := hbc
    _ = 1 * c := (one_mul c).symm
    _ <= a * c := mul_le_mul_left ha c

@[to_additive]

Depends on / 依赖: mul_le_mul_left, one_mul
-/
theorem le_mul_of_one_le_of_le [MulRightMono α] {a b c : α} (ha : 1 <= a)
    (hbc : b <= c) :
    b <= a * c :=
  calc
    b <= c := hbc
    _ = 1 * c := (one_mul c).symm
    _ <= a * c := mul_le_mul_left ha c

@[to_additive]
/--
theorem `lt_mul_of_one_lt_of_le` / 定理 `lt_mul_of_one_lt_of_le`

English:
theorem lt_mul_of_one_lt_of_le
  statement: [MulRightStrictMono α] {a b c : α} (ha : 1 < a)
  proof: calc
    b <= c := hbc
    _ = 1 * c := (one_mul c).symm
    _ < a * c := mul_lt_mul_left ha c

@[to_additive]

中文:
定理 lt_mul_of_one_lt_of_le
  结论: [MulRightStrictMono α] {a b c : α} (ha : 1 < a)
  证明: calc
    b <= c := hbc
    _ = 1 * c := (one_mul c).symm
    _ < a * c := mul_lt_mul_left ha c

@[to_additive]

Depends on / 依赖: mul_lt_mul_left, one_mul
-/
theorem lt_mul_of_one_lt_of_le [MulRightStrictMono α] {a b c : α} (ha : 1 < a)
    (hbc : b <= c) :
    b < a * c :=
  calc
    b <= c := hbc
    _ = 1 * c := (one_mul c).symm
    _ < a * c := mul_lt_mul_left ha c

@[to_additive]
/--
theorem `lt_mul_of_one_le_of_lt` / 定理 `lt_mul_of_one_le_of_lt`

English:
theorem lt_mul_of_one_le_of_lt
  statement: [MulRightMono α] {a b c : α} (ha : 1 <= a)
  proof: calc
    b < c := hbc
    _ = 1 * c := (one_mul c).symm
    _ <= a * c := mul_le_mul_left ha c

@[to_additive]

中文:
定理 lt_mul_of_one_le_of_lt
  结论: [MulRightMono α] {a b c : α} (ha : 1 <= a)
  证明: calc
    b < c := hbc
    _ = 1 * c := (one_mul c).symm
    _ <= a * c := mul_le_mul_left ha c

@[to_additive]

Depends on / 依赖: mul_le_mul_left, one_mul
-/
theorem lt_mul_of_one_le_of_lt [MulRightMono α] {a b c : α} (ha : 1 <= a)
    (hbc : b < c) :
    b < a * c :=
  calc
    b < c := hbc
    _ = 1 * c := (one_mul c).symm
    _ <= a * c := mul_le_mul_left ha c

@[to_additive]
/--
theorem `lt_mul_of_one_lt_of_lt` / 定理 `lt_mul_of_one_lt_of_lt`

English:
theorem lt_mul_of_one_lt_of_lt
  statement: [MulRightStrictMono α] {a b c : α} (ha : 1 < a)
  proof: calc
    b < c := hbc
    _ = 1 * c := (one_mul c).symm
    _ < a * c := mul_lt_mul_left ha c

@[to_additive]

中文:
定理 lt_mul_of_one_lt_of_lt
  结论: [MulRightStrictMono α] {a b c : α} (ha : 1 < a)
  证明: calc
    b < c := hbc
    _ = 1 * c := (one_mul c).symm
    _ < a * c := mul_lt_mul_left ha c

@[to_additive]

Depends on / 依赖: mul_lt_mul_left, one_mul
-/
theorem lt_mul_of_one_lt_of_lt [MulRightStrictMono α] {a b c : α} (ha : 1 < a)
    (hbc : b < c) :
    b < a * c :=
  calc
    b < c := hbc
    _ = 1 * c := (one_mul c).symm
    _ < a * c := mul_lt_mul_left ha c

@[to_additive]
/--
theorem `lt_mul_of_one_lt_of_lt'` / 定理 `lt_mul_of_one_lt_of_lt'`

English:
theorem lt_mul_of_one_lt_of_lt'
  statement: [MulRightMono α] {a b c : α} (ha : 1 < a)
  proof: lt_mul_of_one_le_of_lt ha.le hbc

中文:
定理 lt_mul_of_one_lt_of_lt'
  结论: [MulRightMono α] {a b c : α} (ha : 1 < a)
  证明: lt_mul_of_one_le_of_lt ha.le hbc

Depends on / 依赖: ha.le, lt_mul_of_one_le_of_lt
-/
theorem lt_mul_of_one_lt_of_lt' [MulRightMono α] {a b c : α} (ha : 1 < a)
    (hbc : b < c) :
    b < a * c :=
  lt_mul_of_one_le_of_lt ha.le hbc

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.one_le_mul`. -/
@[to_additive Right.add_nonneg /-- Assumes right covariance.
The lemma assuming left covariance is `Left.add_nonneg`. -/]
/--
theorem `Right.one_le_mul` / 定理 `Right.one_le_mul`

English:
theorem Right.one_le_mul
  statement: [MulRightMono α] {a b : α} (ha : 1 <= a)
  proof: le_mul_of_one_le_of_le ha hb

中文:
定理 Right.one_le_mul
  结论: [MulRightMono α] {a b : α} (ha : 1 <= a)
  证明: le_mul_of_one_le_of_le ha hb

Depends on / 依赖: le_mul_of_one_le_of_le
-/
theorem Right.one_le_mul [MulRightMono α] {a b : α} (ha : 1 <= a)
    (hb : 1 <= b) :
    1 <= a * b :=
  le_mul_of_one_le_of_le ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.one_lt_mul_of_lt_of_le`. -/
@[to_additive Right.add_pos_of_pos_of_nonneg
/-- Assumes right covariance.
The lemma assuming left covariance is `Left.add_pos_of_pos_of_nonneg`. -/]
/--
theorem `Right.one_lt_mul_of_lt_of_le` / 定理 `Right.one_lt_mul_of_lt_of_le`

English:
theorem Right.one_lt_mul_of_lt_of_le
  statement: [MulRightStrictMono α] {a b : α}
  proof: lt_mul_of_one_lt_of_le ha hb

@[to_additive]

中文:
定理 Right.one_lt_mul_of_lt_of_le
  结论: [MulRightStrictMono α] {a b : α}
  证明: lt_mul_of_one_lt_of_le ha hb

@[to_additive]

Depends on / 依赖: lt_mul_of_one_lt_of_le
-/
theorem Right.one_lt_mul_of_lt_of_le [MulRightStrictMono α] {a b : α}
    (ha : 1 < a) (hb : 1 <= b) :
    1 < a * b :=
  lt_mul_of_one_lt_of_le ha hb

@[to_additive]
/--
theorem `Right.one_lt_mul_of_left` / 定理 `Right.one_lt_mul_of_left`

English:
theorem Right.one_lt_mul_of_left
  statement: [IsBotOneClass α] [MulRightStrictMono α] {a : α}
  proof: Right.one_lt_mul_of_lt_of_le ha one_le

中文:
定理 Right.one_lt_mul_of_left
  结论: [是BotOne类 α] [MulRightStrictMono α] {a : α}
  证明: Right.one_lt_mul_of_lt_of_le ha one_le

Depends on / 依赖: Right.one_lt_mul_of_lt_of_le, one_le, one_lt_mul_of_lt_of_le
-/
theorem Right.one_lt_mul_of_left [IsBotOneClass α] [MulRightStrictMono α] {a : α}
    (ha : 1 < a) (b : α) : 1 < a * b :=
  Right.one_lt_mul_of_lt_of_le ha one_le

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.one_lt_mul_of_le_of_lt`. -/
@[to_additive Right.add_pos_of_nonneg_of_pos
/-- Assumes right covariance.
The lemma assuming left covariance is `Left.add_pos_of_nonneg_of_pos`. -/]
/--
theorem `Right.one_lt_mul_of_le_of_lt` / 定理 `Right.one_lt_mul_of_le_of_lt`

English:
theorem Right.one_lt_mul_of_le_of_lt
  statement: [MulRightMono α] {a b : α}
  proof: lt_mul_of_one_le_of_lt ha hb

@[to_additive]

中文:
定理 Right.one_lt_mul_of_le_of_lt
  结论: [MulRightMono α] {a b : α}
  证明: lt_mul_of_one_le_of_lt ha hb

@[to_additive]

Depends on / 依赖: lt_mul_of_one_le_of_lt
-/
theorem Right.one_lt_mul_of_le_of_lt [MulRightMono α] {a b : α}
    (ha : 1 <= a) (hb : 1 < b) :
    1 < a * b :=
  lt_mul_of_one_le_of_lt ha hb

@[to_additive]
/--
theorem `Right.one_lt_mul_of_right` / 定理 `Right.one_lt_mul_of_right`

English:
theorem Right.one_lt_mul_of_right
  statement: [IsBotOneClass α] [MulRightMono α] {b : α}
  proof: Right.one_lt_mul_of_le_of_lt one_le hb

@[to_additive add_pos_of_right] alias one_lt_mul_of_right := Right.one_lt_mul_of_right

中文:
定理 Right.one_lt_mul_of_right
  结论: [是BotOne类 α] [MulRightMono α] {b : α}
  证明: Right.one_lt_mul_of_le_of_lt one_le hb

@[to_additive add_pos_of_right] alias one_lt_mul_of_right := Right.one_lt_mul_of_right

Depends on / 依赖: Right.one_lt_mul_of_le_of_lt, one_le, one_lt_mul_of_le_of_lt
-/
theorem Right.one_lt_mul_of_right [IsBotOneClass α] [MulRightMono α] {b : α}
    (hb : 1 < b) (a : α) : 1 < a * b :=
  Right.one_lt_mul_of_le_of_lt one_le hb

@[to_additive add_pos_of_right] alias one_lt_mul_of_right := Right.one_lt_mul_of_right

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.one_lt_mul`. -/
@[to_additive Right.add_pos /-- Assumes right covariance.
The lemma assuming left covariance is `Left.add_pos`. -/]
/--
theorem `Right.one_lt_mul` / 定理 `Right.one_lt_mul`

English:
theorem Right.one_lt_mul
  statement: [MulRightStrictMono α] {a b : α} (ha : 1 < a)
  proof: lt_mul_of_one_lt_of_lt ha hb

中文:
定理 Right.one_lt_mul
  结论: [MulRightStrictMono α] {a b : α} (ha : 1 < a)
  证明: lt_mul_of_one_lt_of_lt ha hb

Depends on / 依赖: lt_mul_of_one_lt_of_lt
-/
theorem Right.one_lt_mul [MulRightStrictMono α] {a b : α} (ha : 1 < a)
    (hb : 1 < b) :
    1 < a * b :=
  lt_mul_of_one_lt_of_lt ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.one_lt_mul'`. -/
@[to_additive Right.add_pos' /-- Assumes right covariance.
The lemma assuming left covariance is `Left.add_pos'`. -/]
/--
theorem `Right.one_lt_mul'` / 定理 `Right.one_lt_mul'`

English:
theorem Right.one_lt_mul'
  statement: [MulRightMono α] {a b : α} (ha : 1 < a)
  proof: lt_mul_of_one_lt_of_lt' ha hb

alias mul_le_one' := Left.mul_le_one

alias mul_lt_one_of_le_of_lt := Left.mul_lt_one_of_le_of_lt

alias mul_lt_one_of_lt_of_le := Left.mul_lt_one_of_lt_of_le

alias mul_lt_one := Left.mul_lt_one

alias mul_lt_one' := Left.mul_lt_one'

中文:
定理 Right.one_lt_mul'
  结论: [MulRightMono α] {a b : α} (ha : 1 < a)
  证明: lt_mul_of_one_lt_of_lt' ha hb

alias mul_le_one' := Left.mul_le_one

alias mul_lt_one_of_le_of_lt := Left.mul_lt_one_of_le_of_lt

alias mul_lt_one_of_lt_of_le := Left.mul_lt_one_of_lt_of_le

alias mul_lt_one := Left.mul_lt_one

alias mul_lt_one' := Left.mul_lt_one'

Depends on / 依赖: lt_mul_of_one_lt_of_lt
-/
theorem Right.one_lt_mul' [MulRightMono α] {a b : α} (ha : 1 < a)
    (hb : 1 < b) :
    1 < a * b :=
  lt_mul_of_one_lt_of_lt' ha hb

alias mul_le_one' := Left.mul_le_one

alias mul_lt_one_of_le_of_lt := Left.mul_lt_one_of_le_of_lt

alias mul_lt_one_of_lt_of_le := Left.mul_lt_one_of_lt_of_le

alias mul_lt_one := Left.mul_lt_one

alias mul_lt_one' := Left.mul_lt_one'

attribute [to_additive add_nonpos /-- **Alias** of `Left.add_nonpos`. -/] mul_le_one'

attribute [to_additive add_neg_of_nonpos_of_neg
/-- **Alias** of `Left.add_neg_of_nonpos_of_neg`. -/]
  mul_lt_one_of_le_of_lt

attribute [to_additive add_neg_of_neg_of_nonpos
/-- **Alias** of `Left.add_neg_of_neg_of_nonpos`. -/]
  mul_lt_one_of_lt_of_le

attribute [to_additive /-- **Alias** of `Left.add_neg`. -/] mul_lt_one

attribute [to_additive /-- **Alias** of `Left.add_neg'`. -/] mul_lt_one'

alias one_le_mul := Left.one_le_mul

alias one_lt_mul_of_le_of_lt' := Left.one_lt_mul_of_le_of_lt

alias one_lt_mul_of_lt_of_le' := Left.one_lt_mul_of_lt_of_le

alias one_lt_mul' := Left.one_lt_mul

alias one_lt_mul'' := Left.one_lt_mul'

attribute [to_additive add_nonneg /-- **Alias** of `Left.add_nonneg`. -/] one_le_mul

attribute [to_additive add_pos_of_nonneg_of_pos
/-- **Alias** of `Left.add_pos_of_nonneg_of_pos`. -/]
  one_lt_mul_of_le_of_lt'

attribute [to_additive add_pos_of_pos_of_nonneg
/-- **Alias** of `Left.add_pos_of_pos_of_nonneg`. -/]
  one_lt_mul_of_lt_of_le'

attribute [to_additive add_pos /-- **Alias** of `Left.add_pos`. -/] one_lt_mul'

attribute [to_additive add_pos' /-- **Alias** of `Left.add_pos'`. -/] one_lt_mul''

@[to_additive]
/--
theorem `lt_of_mul_lt_of_one_le_left` / 定理 `lt_of_mul_lt_of_one_le_left`

English:
theorem lt_of_mul_lt_of_one_le_left
  statement: [MulLeftMono α] {a b c : α} (h : a * b < c)
  proof: (le_mul_of_one_le_right' hle).trans_lt h

@[to_additive]

中文:
定理 lt_of_mul_lt_of_one_le_left
  结论: [MulLeftMono α] {a b c : α} (h : a * b < c)
  证明: (le_mul_of_one_le_right' hle).trans_lt h

@[to_additive]

Depends on / 依赖: le_mul_of_one_le_right, trans_lt
-/
theorem lt_of_mul_lt_of_one_le_left [MulLeftMono α] {a b c : α} (h : a * b < c)
    (hle : 1 <= b) :
    a < c :=
  (le_mul_of_one_le_right' hle).trans_lt h

@[to_additive]
/--
theorem `le_of_mul_le_of_one_le_left` / 定理 `le_of_mul_le_of_one_le_left`

English:
theorem le_of_mul_le_of_one_le_left
  statement: [MulLeftMono α] {a b c : α} (h : a * b <= c)
  proof: (le_mul_of_one_le_right' hle).trans h

@[to_additive]

中文:
定理 le_of_mul_le_of_one_le_left
  结论: [MulLeftMono α] {a b c : α} (h : a * b <= c)
  证明: (le_mul_of_one_le_right' hle).trans h

@[to_additive]

Depends on / 依赖: le_mul_of_one_le_right
-/
theorem le_of_mul_le_of_one_le_left [MulLeftMono α] {a b c : α} (h : a * b <= c)
    (hle : 1 <= b) :
    a <= c :=
  (le_mul_of_one_le_right' hle).trans h

@[to_additive]
/--
theorem `lt_of_lt_mul_of_le_one_left` / 定理 `lt_of_lt_mul_of_le_one_left`

English:
theorem lt_of_lt_mul_of_le_one_left
  statement: [MulLeftMono α] {a b c : α} (h : a < b * c)
  proof: h.trans_le (mul_le_of_le_one_right' hle)

@[to_additive]

中文:
定理 lt_of_lt_mul_of_le_one_left
  结论: [MulLeftMono α] {a b c : α} (h : a < b * c)
  证明: h.trans_le (mul_le_of_le_one_right' hle)

@[to_additive]

Depends on / 依赖: h.trans_le, mul_le_of_le_one_right, trans_le
-/
theorem lt_of_lt_mul_of_le_one_left [MulLeftMono α] {a b c : α} (h : a < b * c)
    (hle : c <= 1) :
    a < b :=
  h.trans_le (mul_le_of_le_one_right' hle)

@[to_additive]
/--
theorem `le_of_le_mul_of_le_one_left` / 定理 `le_of_le_mul_of_le_one_left`

English:
theorem le_of_le_mul_of_le_one_left
  statement: [MulLeftMono α] {a b c : α} (h : a <= b * c)
  proof: h.trans (mul_le_of_le_one_right' hle)

@[to_additive]

中文:
定理 le_of_le_mul_of_le_one_left
  结论: [MulLeftMono α] {a b c : α} (h : a <= b * c)
  证明: h.trans (mul_le_of_le_one_right' hle)

@[to_additive]

Depends on / 依赖: h.trans, mul_le_of_le_one_right
-/
theorem le_of_le_mul_of_le_one_left [MulLeftMono α] {a b c : α} (h : a <= b * c)
    (hle : c <= 1) :
    a <= b :=
  h.trans (mul_le_of_le_one_right' hle)

@[to_additive]
/--
theorem `lt_of_mul_lt_of_one_le_right` / 定理 `lt_of_mul_lt_of_one_le_right`

English:
theorem lt_of_mul_lt_of_one_le_right
  statement: [MulRightMono α] {a b c : α}
  proof: (le_mul_of_one_le_left' hle).trans_lt h

@[to_additive]

中文:
定理 lt_of_mul_lt_of_one_le_right
  结论: [MulRightMono α] {a b c : α}
  证明: (le_mul_of_one_le_left' hle).trans_lt h

@[to_additive]

Depends on / 依赖: le_mul_of_one_le_left, trans_lt
-/
theorem lt_of_mul_lt_of_one_le_right [MulRightMono α] {a b c : α}
    (h : a * b < c) (hle : 1 <= a) :
    b < c :=
  (le_mul_of_one_le_left' hle).trans_lt h

@[to_additive]
/--
theorem `le_of_mul_le_of_one_le_right` / 定理 `le_of_mul_le_of_one_le_right`

English:
theorem le_of_mul_le_of_one_le_right
  statement: [MulRightMono α] {a b c : α}
  proof: (le_mul_of_one_le_left' hle).trans h

@[to_additive]

中文:
定理 le_of_mul_le_of_one_le_right
  结论: [MulRightMono α] {a b c : α}
  证明: (le_mul_of_one_le_left' hle).trans h

@[to_additive]

Depends on / 依赖: le_mul_of_one_le_left
-/
theorem le_of_mul_le_of_one_le_right [MulRightMono α] {a b c : α}
    (h : a * b <= c) (hle : 1 <= a) :
    b <= c :=
  (le_mul_of_one_le_left' hle).trans h

@[to_additive]
/--
theorem `lt_of_lt_mul_of_le_one_right` / 定理 `lt_of_lt_mul_of_le_one_right`

English:
theorem lt_of_lt_mul_of_le_one_right
  statement: [MulRightMono α] {a b c : α}
  proof: h.trans_le (mul_le_of_le_one_left' hle)

@[to_additive]

中文:
定理 lt_of_lt_mul_of_le_one_right
  结论: [MulRightMono α] {a b c : α}
  证明: h.trans_le (mul_le_of_le_one_left' hle)

@[to_additive]

Depends on / 依赖: h.trans_le, mul_le_of_le_one_left, trans_le
-/
theorem lt_of_lt_mul_of_le_one_right [MulRightMono α] {a b c : α}
    (h : a < b * c) (hle : b <= 1) :
    a < c :=
  h.trans_le (mul_le_of_le_one_left' hle)

@[to_additive]
/--
theorem `le_of_le_mul_of_le_one_right` / 定理 `le_of_le_mul_of_le_one_right`

English:
theorem le_of_le_mul_of_le_one_right
  statement: [MulRightMono α] {a b c : α}
  proof: h.trans (mul_le_of_le_one_left' hle)

中文:
定理 le_of_le_mul_of_le_one_right
  结论: [MulRightMono α] {a b c : α}
  证明: h.trans (mul_le_of_le_one_left' hle)

Depends on / 依赖: h.trans, mul_le_of_le_one_left
-/
theorem le_of_le_mul_of_le_one_right [MulRightMono α] {a b c : α}
    (h : a <= b * c) (hle : b <= 1) :
    a <= c :=
  h.trans (mul_le_of_le_one_left' hle)

end Preorder

section PartialOrder

variable [PartialOrder α]

@[to_additive]
/--
theorem `mul_eq_one_iff_of_one_le` / 定理 `mul_eq_one_iff_of_one_le`

English:
theorem mul_eq_one_iff_of_one_le
  statement: [MulLeftMono α]
  proof: Iff.intro
    (fun hab : a * b = 1 =>
      have : a <= 1 := hab ▸ le_mul_of_le_of_one_le le_rfl hb
      have : a = 1 := le_antisymm this ha
      have : b <= 1 := hab ▸ le_mul_of_one_le_of_le ha le_rfl
      have : b = 1 := le_antisymm this hb
      And.intro ‹a = 1› ‹b = 1›)
    (by rintro ⟨rfl, 

中文:
定理 mul_eq_one_iff_of_one_le
  结论: [MulLeftMono α]
  证明: Iff.intro
    (fun hab : a * b = 1 =>
      have : a <= 1 := hab ▸ le_mul_of_le_of_one_le le_rfl hb
      have : a = 1 := le_antisymm this ha
      have : b <= 1 := hab ▸ le_mul_of_one_le_of_le ha le_rfl
      have : b = 1 := le_antisymm this hb
      And.intro ‹a = 1› ‹b = 1›)
    (by rintro ⟨rfl, 

Depends on / 依赖: And.intro, Iff.intro, le_antisymm, le_mul_of_le_of_one_le, le_mul_of_one_le_of_le, le_rfl, mul_one
-/
theorem mul_eq_one_iff_of_one_le [MulLeftMono α]
    [MulRightMono α] {a b : α} (ha : 1 <= a) (hb : 1 <= b) :
    a * b = 1 ↔ a = 1 ∧ b = 1 :=
  Iff.intro
    (fun hab : a * b = 1 =>
      have : a <= 1 := hab ▸ le_mul_of_le_of_one_le le_rfl hb
      have : a = 1 := le_antisymm this ha
      have : b <= 1 := hab ▸ le_mul_of_one_le_of_le ha le_rfl
      have : b = 1 := le_antisymm this hb
      And.intro ‹a = 1› ‹b = 1›)
    (by rintro ⟨rfl, rfl⟩; rw [mul_one])

section Left

variable [MulLeftMono α] {a b : α}

@[to_additive eq_zero_of_add_nonneg_left]
/--
theorem `eq_one_of_one_le_mul_left` / 定理 `eq_one_of_one_le_mul_left`

English:
theorem eq_one_of_one_le_mul_left
  given: (ha : a <= 1) (hb : b <= 1) (hab : 1 <= a * b)
  statement: a = 1
  proof: ha.eq_of_not_lt fun h => hab.not_gt mul_lt_one_of_lt_of_le h hb

@[to_additive]

中文:
定理 eq_one_of_one_le_mul_left
  条件: (ha : a <= 1) (hb : b <= 1) (hab : 1 <= a * b)
  结论: a = 1
  证明: ha.eq_of_not_lt fun h => hab.not_gt mul_lt_one_of_lt_of_le h hb

@[to_additive]

Depends on / 依赖: eq_of_not_lt, ha.eq_of_not_lt, hab.not_gt, mul_lt_one_of_lt_of_le, not_gt
-/
theorem eq_one_of_one_le_mul_left (ha : a <= 1) (hb : b <= 1) (hab : 1 <= a * b) : a = 1 :=
ha.eq_of_not_lt fun h => hab.not_gt mul_lt_one_of_lt_of_le h hb

@[to_additive]
/--
theorem `eq_one_of_mul_le_one_left` / 定理 `eq_one_of_mul_le_one_left`

English:
theorem eq_one_of_mul_le_one_left
  given: (ha : 1 <= a) (hb : 1 <= b) (hab : a * b <= 1)
  statement: a = 1
  proof: ha.eq_of_not_lt' fun h => hab.not_gt one_lt_mul_of_lt_of_le' h hb

中文:
定理 eq_one_of_mul_le_one_left
  条件: (ha : 1 <= a) (hb : 1 <= b) (hab : a * b <= 1)
  结论: a = 1
  证明: ha.eq_of_not_lt' fun h => hab.not_gt one_lt_mul_of_lt_of_le' h hb

Depends on / 依赖: eq_of_not_lt, ha.eq_of_not_lt, hab.not_gt, not_gt, one_lt_mul_of_lt_of_le
-/
theorem eq_one_of_mul_le_one_left (ha : 1 <= a) (hb : 1 <= b) (hab : a * b <= 1) : a = 1 :=
ha.eq_of_not_lt' fun h => hab.not_gt one_lt_mul_of_lt_of_le' h hb

end Left

section Right

variable [MulRightMono α] {a b : α}

@[to_additive eq_zero_of_add_nonneg_right]
/--
theorem `eq_one_of_one_le_mul_right` / 定理 `eq_one_of_one_le_mul_right`

English:
theorem eq_one_of_one_le_mul_right
  given: (ha : a <= 1) (hb : b <= 1) (hab : 1 <= a * b)
  statement: b = 1
  proof: hb.eq_of_not_lt fun h => hab.not_gt Right.mul_lt_one_of_le_of_lt ha h

@[to_additive]

中文:
定理 eq_one_of_one_le_mul_right
  条件: (ha : a <= 1) (hb : b <= 1) (hab : 1 <= a * b)
  结论: b = 1
  证明: hb.eq_of_not_lt fun h => hab.not_gt Right.mul_lt_one_of_le_of_lt ha h

@[to_additive]

Depends on / 依赖: Right.mul_lt_one_of_le_of_lt, eq_of_not_lt, hab.not_gt, hb.eq_of_not_lt, mul_lt_one_of_le_of_lt, not_gt
-/
theorem eq_one_of_one_le_mul_right (ha : a <= 1) (hb : b <= 1) (hab : 1 <= a * b) : b = 1 :=
hb.eq_of_not_lt fun h => hab.not_gt Right.mul_lt_one_of_le_of_lt ha h

@[to_additive]
/--
theorem `eq_one_of_mul_le_one_right` / 定理 `eq_one_of_mul_le_one_right`

English:
theorem eq_one_of_mul_le_one_right
  given: (ha : 1 <= a) (hb : 1 <= b) (hab : a * b <= 1)
  statement: b = 1
  proof: hb.eq_of_not_lt' fun h => hab.not_gt Right.one_lt_mul_of_le_of_lt ha h

中文:
定理 eq_one_of_mul_le_one_right
  条件: (ha : 1 <= a) (hb : 1 <= b) (hab : a * b <= 1)
  结论: b = 1
  证明: hb.eq_of_not_lt' fun h => hab.not_gt Right.one_lt_mul_of_le_of_lt ha h

Depends on / 依赖: Right.one_lt_mul_of_le_of_lt, eq_of_not_lt, hab.not_gt, hb.eq_of_not_lt, not_gt, one_lt_mul_of_le_of_lt
-/
theorem eq_one_of_mul_le_one_right (ha : 1 <= a) (hb : 1 <= b) (hab : a * b <= 1) : b = 1 :=
hb.eq_of_not_lt' fun h => hab.not_gt Right.one_lt_mul_of_le_of_lt ha h

end Right

end PartialOrder

section LinearOrder

variable [LinearOrder α]

/--
theorem `exists_square_le` / 定理 `exists_square_le`

English:
theorem exists_square_le
  given: [MulLeftStrictMono α] (a : α)
  statement: exists b : α, b * b <= a
  proof: by
  by_cases! h : a < 1
  · use a
    have : a * a < a * 1 := mul_lt_mul_right h a
    rw [mul_one] at this
    exact le_of_lt this
  · use 1
    rwa [mul_one]

中文:
定理 存在_square_le
  条件: [MulLeftStrictMono α] (a : α)
  结论: 存在 b : α, b * b <= a
  证明: by
  by_cases! h : a < 1
  · use a
    have : a * a < a * 1 := mul_lt_mul_right h a
    rw [mul_one] at this
    exact le_of_lt this
  · use 1
    rwa [mul_one]

Depends on / 依赖: le_of_lt, mul_lt_mul_right, mul_one
-/
theorem exists_square_le [MulLeftStrictMono α] (a : α) : exists b : α, b * b <= a := by
  by_cases! h : a < 1
  · use a
    have : a * a < a * 1 := mul_lt_mul_right h a
    rw [mul_one] at this
    exact le_of_lt this
  · use 1
    rwa [mul_one]

end LinearOrder

end MulOneClass

section Semigroup

variable [Semigroup α]

section PartialOrder

variable [PartialOrder α]

/- This is not instance, since we want to have an instance from `LeftCancelSemigroup`s
to the appropriate covariant class. -/
/-- A semigroup with a partial order and satisfying `LeftCancelSemigroup`
(i.e. `a * c < b * c → a < b`) is a `LeftCancelSemigroup`. -/
@[to_additive (attr := instance_reducible)
/-- An additive semigroup with a partial order and satisfying `AddLeftCancelSemigroup`
(i.e. `c + a < c + b → a < b`) is a `AddLeftCancelSemigroup`. -/]
/--
Definition of `Contravariant.toLeftCancelSemigroup` / `Contravariant.toLeftCancelSemigroup` 的定义

English:
definition Contravariant.toLeftCancelSemigroup
  signature: [MulLeftReflectLE α]

中文:
定义 Contravariant.toLeftCancelSemigroup
  签名: [MulLeftReflectLE α]
-/
def Contravariant.toLeftCancelSemigroup [MulLeftReflectLE α] : LeftCancelSemigroup α where

/- This is not instance, since we want to have an instance from `RightCancelSemigroup`s
to the appropriate covariant class. -/
/-- A semigroup with a partial order and satisfying `RightCancelSemigroup`
(i.e. `a * c < b * c → a < b`) is a `RightCancelSemigroup`. -/
@[to_additive (attr := instance_reducible)
/-- An additive semigroup with a partial order and satisfying `AddRightCancelSemigroup`
(`a + c < b + c → a < b`) is a `AddRightCancelSemigroup`. -/]
/--
Definition of `Contravariant.toRightCancelSemigroup` / `Contravariant.toRightCancelSemigroup` 的定义

English:
definition Contravariant.toRightCancelSemigroup
  signature: [MulRightReflectLE α]

中文:
定义 Contravariant.toRightCancelSemigroup
  签名: [MulRightReflectLE α]
-/
def Contravariant.toRightCancelSemigroup [MulRightReflectLE α] : RightCancelSemigroup α where

end PartialOrder

end Semigroup

section Mono

variable [Mul α] [Preorder α] [Preorder β] {f g : β -> α} {s : Set β}

@[to_additive const_add]
/--
theorem `Monotone.const_mul'` / 定理 `Monotone.const_mul'`

English:
theorem Monotone.const_mul'
  given: [MulLeftMono α] (hf : Monotone f) (a : α)
  statement: Monotone fun x => a * f x
  proof: mul_right_mono.comp hf

@[to_additive const_add]

中文:
定理 递增.const_mul'
  条件: [MulLeftMono α] (hf : 递增 f) (a : α)
  结论: 递增 fun x => a * f x
  证明: mul_right_mono.comp hf

@[to_additive const_add]

Depends on / 依赖: mul_right_mono, mul_right_mono.comp
-/
theorem Monotone.const_mul' [MulLeftMono α] (hf : Monotone f) (a : α) : Monotone fun x => a * f x :=
  mul_right_mono.comp hf

@[to_additive const_add]
/--
theorem `MonotoneOn.const_mul'` / 定理 `MonotoneOn.const_mul'`

English:
theorem MonotoneOn.const_mul'
  given: [MulLeftMono α] (hf : MonotoneOn f s) (a : α)
  proof: mul_right_mono.comp_monotoneOn hf

@[to_additive const_add]

中文:
定理 MonotoneOn.const_mul'
  条件: [MulLeftMono α] (hf : MonotoneOn f s) (a : α)
  证明: mul_right_mono.comp_monotoneOn hf

@[to_additive const_add]

Depends on / 依赖: comp_monotoneOn, mul_right_mono, mul_right_mono.comp_monotoneOn
-/
theorem MonotoneOn.const_mul' [MulLeftMono α] (hf : MonotoneOn f s) (a : α) :
    MonotoneOn (fun x => a * f x) s := mul_right_mono.comp_monotoneOn hf

@[to_additive const_add]
/--
theorem `Antitone.const_mul'` / 定理 `Antitone.const_mul'`

English:
theorem Antitone.const_mul'
  given: [MulLeftMono α] (hf : Antitone f) (a : α)
  statement: Antitone fun x => a * f x
  proof: mul_right_mono.comp_antitone hf

@[to_additive const_add]

中文:
定理 递减.const_mul'
  条件: [MulLeftMono α] (hf : 递减 f) (a : α)
  结论: 递减 fun x => a * f x
  证明: mul_right_mono.comp_antitone hf

@[to_additive const_add]

Depends on / 依赖: comp_antitone, mul_right_mono, mul_right_mono.comp_antitone
-/
theorem Antitone.const_mul' [MulLeftMono α] (hf : Antitone f) (a : α) : Antitone fun x => a * f x :=
  mul_right_mono.comp_antitone hf

@[to_additive const_add]
/--
theorem `AntitoneOn.const_mul'` / 定理 `AntitoneOn.const_mul'`

English:
theorem AntitoneOn.const_mul'
  given: [MulLeftMono α] (hf : AntitoneOn f s) (a : α)
  proof: mul_right_mono.comp_antitoneOn hf

@[to_additive add_const]

中文:
定理 AntitoneOn.const_mul'
  条件: [MulLeftMono α] (hf : AntitoneOn f s) (a : α)
  证明: mul_right_mono.comp_antitoneOn hf

@[to_additive add_const]

Depends on / 依赖: comp_antitoneOn, mul_right_mono, mul_right_mono.comp_antitoneOn
-/
theorem AntitoneOn.const_mul' [MulLeftMono α] (hf : AntitoneOn f s) (a : α) :
    AntitoneOn (fun x => a * f x) s := mul_right_mono.comp_antitoneOn hf

@[to_additive add_const]
/--
theorem `Monotone.mul_const'` / 定理 `Monotone.mul_const'`

English:
theorem Monotone.mul_const'
  given: [MulRightMono α] (hf : Monotone f) (a : α)
  proof: mul_left_mono.comp hf

@[to_additive add_const]

中文:
定理 递增.mul_const'
  条件: [MulRightMono α] (hf : 递增 f) (a : α)
  证明: mul_left_mono.comp hf

@[to_additive add_const]

Depends on / 依赖: mul_left_mono, mul_left_mono.comp
-/
theorem Monotone.mul_const' [MulRightMono α] (hf : Monotone f) (a : α) :
    Monotone fun x => f x * a := mul_left_mono.comp hf

@[to_additive add_const]
/--
theorem `MonotoneOn.mul_const'` / 定理 `MonotoneOn.mul_const'`

English:
theorem MonotoneOn.mul_const'
  given: [MulRightMono α] (hf : MonotoneOn f s) (a : α)
  proof: mul_left_mono.comp_monotoneOn hf

@[to_additive add_const]

中文:
定理 MonotoneOn.mul_const'
  条件: [MulRightMono α] (hf : MonotoneOn f s) (a : α)
  证明: mul_left_mono.comp_monotoneOn hf

@[to_additive add_const]

Depends on / 依赖: comp_monotoneOn, mul_left_mono, mul_left_mono.comp_monotoneOn
-/
theorem MonotoneOn.mul_const' [MulRightMono α] (hf : MonotoneOn f s) (a : α) :
    MonotoneOn (fun x => f x * a) s := mul_left_mono.comp_monotoneOn hf

@[to_additive add_const]
/--
theorem `Antitone.mul_const'` / 定理 `Antitone.mul_const'`

English:
theorem Antitone.mul_const'
  given: [MulRightMono α] (hf : Antitone f) (a : α)
  statement: Antitone fun x => f x * a
  proof: mul_left_mono.comp_antitone hf

@[to_additive add_const]

中文:
定理 递减.mul_const'
  条件: [MulRightMono α] (hf : 递减 f) (a : α)
  结论: 递减 fun x => f x * a
  证明: mul_left_mono.comp_antitone hf

@[to_additive add_const]

Depends on / 依赖: comp_antitone, mul_left_mono, mul_left_mono.comp_antitone
-/
theorem Antitone.mul_const' [MulRightMono α] (hf : Antitone f) (a : α) : Antitone fun x => f x * a :=
  mul_left_mono.comp_antitone hf

@[to_additive add_const]
/--
theorem `AntitoneOn.mul_const'` / 定理 `AntitoneOn.mul_const'`

English:
theorem AntitoneOn.mul_const'
  given: [MulRightMono α] (hf : AntitoneOn f s) (a : α)
  proof: mul_left_mono.comp_antitoneOn hf

中文:
定理 AntitoneOn.mul_const'
  条件: [MulRightMono α] (hf : AntitoneOn f s) (a : α)
  证明: mul_left_mono.comp_antitoneOn hf

Depends on / 依赖: comp_antitoneOn, mul_left_mono, mul_left_mono.comp_antitoneOn
-/
theorem AntitoneOn.mul_const' [MulRightMono α] (hf : AntitoneOn f s) (a : α) :
    AntitoneOn (fun x => f x * a) s := mul_left_mono.comp_antitoneOn hf

/-- The product of two monotone functions is monotone. -/
@[to_additive add /-- The sum of two monotone functions is monotone. -/]
/--
theorem `Monotone.mul'` / 定理 `Monotone.mul'`

English:
theorem Monotone.mul'
  statement: [MulLeftMono α]
  proof: fun _ _ h => mul_le_mul' (hf h) (hg h)

中文:
定理 递增.mul'
  结论: [MulLeftMono α]
  证明: fun _ _ h => mul_le_mul' (hf h) (hg h)

Depends on / 依赖: mul_le_mul
-/
theorem Monotone.mul' [MulLeftMono α]
    [MulRightMono α] (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x * g x := fun _ _ h => mul_le_mul' (hf h) (hg h)

/-- The product of two monotone functions is monotone. -/
@[to_additive add /-- The sum of two monotone functions is monotone. -/]
/--
theorem `MonotoneOn.mul'` / 定理 `MonotoneOn.mul'`

English:
theorem MonotoneOn.mul'
  statement: [MulLeftMono α]
  proof: fun _ hx _ hy h =>
  mul_le_mul' (hf hx hy h) (hg hx hy h)

中文:
定理 MonotoneOn.mul'
  结论: [MulLeftMono α]
  证明: fun _ hx _ hy h =>
  mul_le_mul' (hf hx hy h) (hg hx hy h)
-/
theorem MonotoneOn.mul' [MulLeftMono α]
    [MulRightMono α] (hf : MonotoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => f x * g x) s := fun _ hx _ hy h =>
  mul_le_mul' (hf hx hy h) (hg hx hy h)

/-- The product of two antitone functions is antitone. -/
@[to_additive add /-- The sum of two antitone functions is antitone. -/]
/--
theorem `Antitone.mul'` / 定理 `Antitone.mul'`

English:
theorem Antitone.mul'
  statement: [MulLeftMono α]
  proof: fun _ _ h => mul_le_mul' (hf h) (hg h)

中文:
定理 递减.mul'
  结论: [MulLeftMono α]
  证明: fun _ _ h => mul_le_mul' (hf h) (hg h)

Depends on / 依赖: mul_le_mul
-/
theorem Antitone.mul' [MulLeftMono α]
    [MulRightMono α] (hf : Antitone f) (hg : Antitone g) :
    Antitone fun x => f x * g x := fun _ _ h => mul_le_mul' (hf h) (hg h)

/-- The product of two antitone functions is antitone. -/
@[to_additive add /-- The sum of two antitone functions is antitone. -/]
/--
theorem `AntitoneOn.mul'` / 定理 `AntitoneOn.mul'`

English:
theorem AntitoneOn.mul'
  statement: [MulLeftMono α]
  proof: fun _ hx _ hy h => mul_le_mul' (hf hx hy h) (hg hx hy h)

中文:
定理 AntitoneOn.mul'
  结论: [MulLeftMono α]
  证明: fun _ hx _ hy h => mul_le_mul' (hf hx hy h) (hg hx hy h)

Depends on / 依赖: mul_le_mul
-/
theorem AntitoneOn.mul' [MulLeftMono α]
    [MulRightMono α] (hf : AntitoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => f x * g x) s :=
  fun _ hx _ hy h => mul_le_mul' (hf hx hy h) (hg hx hy h)

section Left

variable [MulLeftStrictMono α]

@[to_additive const_add]
/--
theorem `StrictMono.const_mul'` / 定理 `StrictMono.const_mul'`

English:
theorem StrictMono.const_mul'
  given: (hf : StrictMono f) (c : α)
  statement: StrictMono fun x => c * f x
  proof: fun _ _ ab => mul_lt_mul_right (hf ab) c

@[to_additive const_add]

中文:
定理 严格递增.const_mul'
  条件: (hf : 严格递增 f) (c : α)
  结论: 严格递增 fun x => c * f x
  证明: fun _ _ ab => mul_lt_mul_right (hf ab) c

@[to_additive const_add]

Depends on / 依赖: mul_lt_mul_right
-/
theorem StrictMono.const_mul' (hf : StrictMono f) (c : α) : StrictMono fun x => c * f x :=
  fun _ _ ab => mul_lt_mul_right (hf ab) c

@[to_additive const_add]
/--
theorem `StrictMonoOn.const_mul'` / 定理 `StrictMonoOn.const_mul'`

English:
theorem StrictMonoOn.const_mul'
  given: (hf : StrictMonoOn f s) (c : α)
  proof: fun _ ha _ hb ab => mul_lt_mul_right (hf ha hb ab) c

@[to_additive const_add]

中文:
定理 StrictMonoOn.const_mul'
  条件: (hf : StrictMonoOn f s) (c : α)
  证明: fun _ ha _ hb ab => mul_lt_mul_right (hf ha hb ab) c

@[to_additive const_add]

Depends on / 依赖: mul_lt_mul_right
-/
theorem StrictMonoOn.const_mul' (hf : StrictMonoOn f s) (c : α) :
    StrictMonoOn (fun x => c * f x) s :=
  fun _ ha _ hb ab => mul_lt_mul_right (hf ha hb ab) c

@[to_additive const_add]
/--
theorem `StrictAnti.const_mul'` / 定理 `StrictAnti.const_mul'`

English:
theorem StrictAnti.const_mul'
  given: (hf : StrictAnti f) (c : α)
  statement: StrictAnti fun x => c * f x
  proof: fun _ _ ab => mul_lt_mul_right (hf ab) c

@[to_additive const_add]

中文:
定理 严格递减.const_mul'
  条件: (hf : 严格递减 f) (c : α)
  结论: 严格递减 fun x => c * f x
  证明: fun _ _ ab => mul_lt_mul_right (hf ab) c

@[to_additive const_add]

Depends on / 依赖: mul_lt_mul_right
-/
theorem StrictAnti.const_mul' (hf : StrictAnti f) (c : α) : StrictAnti fun x => c * f x :=
  fun _ _ ab => mul_lt_mul_right (hf ab) c

@[to_additive const_add]
/--
theorem `StrictAntiOn.const_mul'` / 定理 `StrictAntiOn.const_mul'`

English:
theorem StrictAntiOn.const_mul'
  given: (hf : StrictAntiOn f s) (c : α)
  proof: fun _ ha _ hb ab => mul_lt_mul_right (hf ha hb ab) c

中文:
定理 StrictAntiOn.const_mul'
  条件: (hf : StrictAntiOn f s) (c : α)
  证明: fun _ ha _ hb ab => mul_lt_mul_right (hf ha hb ab) c

Depends on / 依赖: mul_lt_mul_right
-/
theorem StrictAntiOn.const_mul' (hf : StrictAntiOn f s) (c : α) :
    StrictAntiOn (fun x => c * f x) s :=
  fun _ ha _ hb ab => mul_lt_mul_right (hf ha hb ab) c

end Left

section Right

variable [MulRightStrictMono α]

@[to_additive add_const]
/--
theorem `StrictMono.mul_const'` / 定理 `StrictMono.mul_const'`

English:
theorem StrictMono.mul_const'
  given: (hf : StrictMono f) (c : α)
  statement: StrictMono fun x => f x * c
  proof: fun _ _ ab => mul_lt_mul_left (hf ab) c

@[to_additive add_const]

中文:
定理 严格递增.mul_const'
  条件: (hf : 严格递增 f) (c : α)
  结论: 严格递增 fun x => f x * c
  证明: fun _ _ ab => mul_lt_mul_left (hf ab) c

@[to_additive add_const]

Depends on / 依赖: mul_lt_mul_left
-/
theorem StrictMono.mul_const' (hf : StrictMono f) (c : α) : StrictMono fun x => f x * c :=
  fun _ _ ab => mul_lt_mul_left (hf ab) c

@[to_additive add_const]
/--
theorem `StrictMonoOn.mul_const'` / 定理 `StrictMonoOn.mul_const'`

English:
theorem StrictMonoOn.mul_const'
  given: (hf : StrictMonoOn f s) (c : α)
  proof: fun _ ha _ hb ab => mul_lt_mul_left (hf ha hb ab) c

@[to_additive add_const]

中文:
定理 StrictMonoOn.mul_const'
  条件: (hf : StrictMonoOn f s) (c : α)
  证明: fun _ ha _ hb ab => mul_lt_mul_left (hf ha hb ab) c

@[to_additive add_const]

Depends on / 依赖: mul_lt_mul_left
-/
theorem StrictMonoOn.mul_const' (hf : StrictMonoOn f s) (c : α) :
    StrictMonoOn (fun x => f x * c) s :=
  fun _ ha _ hb ab => mul_lt_mul_left (hf ha hb ab) c

@[to_additive add_const]
/--
theorem `StrictAnti.mul_const'` / 定理 `StrictAnti.mul_const'`

English:
theorem StrictAnti.mul_const'
  given: (hf : StrictAnti f) (c : α)
  statement: StrictAnti fun x => f x * c
  proof: fun _ _ ab => mul_lt_mul_left (hf ab) c

@[to_additive add_const]

中文:
定理 严格递减.mul_const'
  条件: (hf : 严格递减 f) (c : α)
  结论: 严格递减 fun x => f x * c
  证明: fun _ _ ab => mul_lt_mul_left (hf ab) c

@[to_additive add_const]

Depends on / 依赖: mul_lt_mul_left
-/
theorem StrictAnti.mul_const' (hf : StrictAnti f) (c : α) : StrictAnti fun x => f x * c :=
  fun _ _ ab => mul_lt_mul_left (hf ab) c

@[to_additive add_const]
/--
theorem `StrictAntiOn.mul_const'` / 定理 `StrictAntiOn.mul_const'`

English:
theorem StrictAntiOn.mul_const'
  given: (hf : StrictAntiOn f s) (c : α)
  proof: fun _ ha _ hb ab => mul_lt_mul_left (hf ha hb ab) c

中文:
定理 StrictAntiOn.mul_const'
  条件: (hf : StrictAntiOn f s) (c : α)
  证明: fun _ ha _ hb ab => mul_lt_mul_left (hf ha hb ab) c

Depends on / 依赖: mul_lt_mul_left
-/
theorem StrictAntiOn.mul_const' (hf : StrictAntiOn f s) (c : α) :
    StrictAntiOn (fun x => f x * c) s :=
  fun _ ha _ hb ab => mul_lt_mul_left (hf ha hb ab) c

end Right

/-- The product of two strictly monotone functions is strictly monotone. -/
@[to_additive add /-- The sum of two strictly monotone functions is strictly monotone. -/]
/--
theorem `StrictMono.mul'` / 定理 `StrictMono.mul'`

English:
theorem StrictMono.mul'
  statement: [MulLeftStrictMono α]
  proof: fun _ _ ab =>
  mul_lt_mul_of_lt_of_lt (hf ab) (hg ab)

中文:
定理 严格递增.mul'
  结论: [MulLeftStrictMono α]
  证明: fun _ _ ab =>
  mul_lt_mul_of_lt_of_lt (hf ab) (hg ab)
-/
theorem StrictMono.mul' [MulLeftStrictMono α]
    [MulRightStrictMono α] (hf : StrictMono f) (hg : StrictMono g) :
    StrictMono fun x => f x * g x := fun _ _ ab =>
  mul_lt_mul_of_lt_of_lt (hf ab) (hg ab)

/-- The product of two strictly monotone functions is strictly monotone. -/
@[to_additive add /-- The sum of two strictly monotone functions is strictly monotone. -/]
/--
theorem `StrictMonoOn.mul'` / 定理 `StrictMonoOn.mul'`

English:
theorem StrictMonoOn.mul'
  statement: [MulLeftStrictMono α]
  proof: fun _ ha _ hb ab => mul_lt_mul_of_lt_of_lt (hf ha hb ab) (hg ha hb ab)

中文:
定理 StrictMonoOn.mul'
  结论: [MulLeftStrictMono α]
  证明: fun _ ha _ hb ab => mul_lt_mul_of_lt_of_lt (hf ha hb ab) (hg ha hb ab)

Depends on / 依赖: mul_lt_mul_of_lt_of_lt
-/
theorem StrictMonoOn.mul' [MulLeftStrictMono α]
    [MulRightStrictMono α] (hf : StrictMonoOn f s) (hg : StrictMonoOn g s) :
    StrictMonoOn (fun x => f x * g x) s :=
  fun _ ha _ hb ab => mul_lt_mul_of_lt_of_lt (hf ha hb ab) (hg ha hb ab)

/-- The product of two strictly antitone functions is strictly antitone. -/
@[to_additive add /-- The sum of two strictly antitone functions is strictly antitone. -/]
/--
theorem `StrictAnti.mul'` / 定理 `StrictAnti.mul'`

English:
theorem StrictAnti.mul'
  statement: [MulLeftStrictMono α]
  proof: fun _ _ ab => mul_lt_mul_of_lt_of_lt (hf ab) (hg ab)

中文:
定理 严格递减.mul'
  结论: [MulLeftStrictMono α]
  证明: fun _ _ ab => mul_lt_mul_of_lt_of_lt (hf ab) (hg ab)

Depends on / 依赖: mul_lt_mul_of_lt_of_lt
-/
theorem StrictAnti.mul' [MulLeftStrictMono α]
    [MulRightStrictMono α] (hf : StrictAnti f) (hg : StrictAnti g) :
    StrictAnti fun x => f x * g x :=
  fun _ _ ab => mul_lt_mul_of_lt_of_lt (hf ab) (hg ab)

/-- The product of two strictly antitone functions is strictly antitone. -/
@[to_additive add /-- The sum of two strictly antitone functions is strictly antitone. -/]
/--
theorem `StrictAntiOn.mul'` / 定理 `StrictAntiOn.mul'`

English:
theorem StrictAntiOn.mul'
  statement: [MulLeftStrictMono α]
  proof: fun _ ha _ hb ab => mul_lt_mul_of_lt_of_lt (hf ha hb ab) (hg ha hb ab)

中文:
定理 StrictAntiOn.mul'
  结论: [MulLeftStrictMono α]
  证明: fun _ ha _ hb ab => mul_lt_mul_of_lt_of_lt (hf ha hb ab) (hg ha hb ab)

Depends on / 依赖: mul_lt_mul_of_lt_of_lt
-/
theorem StrictAntiOn.mul' [MulLeftStrictMono α]
    [MulRightStrictMono α] (hf : StrictAntiOn f s) (hg : StrictAntiOn g s) :
    StrictAntiOn (fun x => f x * g x) s :=
  fun _ ha _ hb ab => mul_lt_mul_of_lt_of_lt (hf ha hb ab) (hg ha hb ab)

/-- The product of a monotone function and a strictly monotone function is strictly monotone. -/
@[to_additive add_strictMono /-- The sum of a monotone function and a strictly monotone function is
strictly monotone. -/]
/--
theorem `Monotone.mul_strictMono'` / 定理 `Monotone.mul_strictMono'`

English:
theorem Monotone.mul_strictMono'
  statement: [MulLeftStrictMono α]
  proof: fun _ _ h => mul_lt_mul_of_le_of_lt (hf h.le) (hg h)

中文:
定理 递增.mul_strictMono'
  结论: [MulLeftStrictMono α]
  证明: fun _ _ h => mul_lt_mul_of_le_of_lt (hf h.le) (hg h)

Depends on / 依赖: h.le, mul_lt_mul_of_le_of_lt
-/
theorem Monotone.mul_strictMono' [MulLeftStrictMono α]
    [MulRightMono α] {f g : β -> α} (hf : Monotone f)
    (hg : StrictMono g) :
    StrictMono fun x => f x * g x :=
  fun _ _ h => mul_lt_mul_of_le_of_lt (hf h.le) (hg h)

/-- The product of a monotone function and a strictly monotone function is strictly monotone. -/
@[to_additive add_strictMono /-- The sum of a monotone function and a strictly monotone function is
strictly monotone. -/]
/--
theorem `MonotoneOn.mul_strictMono'` / 定理 `MonotoneOn.mul_strictMono'`

English:
theorem MonotoneOn.mul_strictMono'
  statement: [MulLeftStrictMono α]
  proof: fun _ hx _ hy h => mul_lt_mul_of_le_of_lt (hf hx hy h.le) (hg hx hy h)

中文:
定理 MonotoneOn.mul_strictMono'
  结论: [MulLeftStrictMono α]
  证明: fun _ hx _ hy h => mul_lt_mul_of_le_of_lt (hf hx hy h.le) (hg hx hy h)

Depends on / 依赖: h.le, mul_lt_mul_of_le_of_lt
-/
theorem MonotoneOn.mul_strictMono' [MulLeftStrictMono α]
    [MulRightMono α] {f g : β -> α} (hf : MonotoneOn f s)
    (hg : StrictMonoOn g s) : StrictMonoOn (fun x => f x * g x) s :=
  fun _ hx _ hy h => mul_lt_mul_of_le_of_lt (hf hx hy h.le) (hg hx hy h)

/-- The product of an antitone function and a strictly antitone function is strictly antitone. -/
@[to_additive add_strictAnti /-- The sum of an antitone function and a strictly antitone function is
strictly antitone. -/]
/--
theorem `Antitone.mul_strictAnti'` / 定理 `Antitone.mul_strictAnti'`

English:
theorem Antitone.mul_strictAnti'
  statement: [MulLeftStrictMono α]
  proof: fun _ _ h => mul_lt_mul_of_le_of_lt (hf h.le) (hg h)

中文:
定理 递减.mul_strictAnti'
  结论: [MulLeftStrictMono α]
  证明: fun _ _ h => mul_lt_mul_of_le_of_lt (hf h.le) (hg h)

Depends on / 依赖: h.le, mul_lt_mul_of_le_of_lt
-/
theorem Antitone.mul_strictAnti' [MulLeftStrictMono α]
    [MulRightMono α] {f g : β -> α} (hf : Antitone f)
    (hg : StrictAnti g) :
    StrictAnti fun x => f x * g x :=
  fun _ _ h => mul_lt_mul_of_le_of_lt (hf h.le) (hg h)

/-- The product of an antitone function and a strictly antitone function is strictly antitone. -/
@[to_additive add_strictAnti /-- The sum of an antitone function and a strictly antitone function is
strictly antitone. -/]
/--
theorem `AntitoneOn.mul_strictAnti'` / 定理 `AntitoneOn.mul_strictAnti'`

English:
theorem AntitoneOn.mul_strictAnti'
  statement: [MulLeftStrictMono α]
  proof: fun _ hx _ hy h => mul_lt_mul_of_le_of_lt (hf hx hy h.le) (hg hx hy h)

中文:
定理 AntitoneOn.mul_strictAnti'
  结论: [MulLeftStrictMono α]
  证明: fun _ hx _ hy h => mul_lt_mul_of_le_of_lt (hf hx hy h.le) (hg hx hy h)

Depends on / 依赖: h.le, mul_lt_mul_of_le_of_lt
-/
theorem AntitoneOn.mul_strictAnti' [MulLeftStrictMono α]
    [MulRightMono α] {f g : β -> α} (hf : AntitoneOn f s)
    (hg : StrictAntiOn g s) :
    StrictAntiOn (fun x => f x * g x) s :=
  fun _ hx _ hy h => mul_lt_mul_of_le_of_lt (hf hx hy h.le) (hg hx hy h)

variable [MulLeftMono α] [MulRightStrictMono α]

/-- The product of a strictly monotone function and a monotone function is strictly monotone. -/
@[to_additive add_monotone /-- The sum of a strictly monotone function and a monotone function is
strictly monotone. -/]
/--
theorem `StrictMono.mul_monotone'` / 定理 `StrictMono.mul_monotone'`

English:
theorem StrictMono.mul_monotone'
  given: (hf : StrictMono f) (hg : Monotone g)
  proof: fun _ _ h => mul_lt_mul_of_lt_of_le (hf h) (hg h.le)

中文:
定理 严格递增.mul_monotone'
  条件: (hf : 严格递增 f) (hg : 递增 g)
  证明: fun _ _ h => mul_lt_mul_of_lt_of_le (hf h) (hg h.le)

Depends on / 依赖: h.le, mul_lt_mul_of_lt_of_le
-/
theorem StrictMono.mul_monotone' (hf : StrictMono f) (hg : Monotone g) :
    StrictMono fun x => f x * g x :=
  fun _ _ h => mul_lt_mul_of_lt_of_le (hf h) (hg h.le)

/-- The product of a strictly monotone function and a monotone function is strictly monotone. -/
@[to_additive add_monotone /-- The sum of a strictly monotone function and a monotone function is
strictly monotone. -/]
/--
theorem `StrictMonoOn.mul_monotone'` / 定理 `StrictMonoOn.mul_monotone'`

English:
theorem StrictMonoOn.mul_monotone'
  given: (hf : StrictMonoOn f s) (hg : MonotoneOn g s)
  proof: fun _ hx _ hy h => mul_lt_mul_of_lt_of_le (hf hx hy h) (hg hx hy h.le)

中文:
定理 StrictMonoOn.mul_monotone'
  条件: (hf : StrictMonoOn f s) (hg : MonotoneOn g s)
  证明: fun _ hx _ hy h => mul_lt_mul_of_lt_of_le (hf hx hy h) (hg hx hy h.le)

Depends on / 依赖: h.le, mul_lt_mul_of_lt_of_le
-/
theorem StrictMonoOn.mul_monotone' (hf : StrictMonoOn f s) (hg : MonotoneOn g s) :
    StrictMonoOn (fun x => f x * g x) s :=
  fun _ hx _ hy h => mul_lt_mul_of_lt_of_le (hf hx hy h) (hg hx hy h.le)

/-- The product of a strictly antitone function and an antitone function is strictly antitone. -/
@[to_additive add_antitone /-- The sum of a strictly antitone function and an antitone function is
strictly antitone. -/]
/--
theorem `StrictAnti.mul_antitone'` / 定理 `StrictAnti.mul_antitone'`

English:
theorem StrictAnti.mul_antitone'
  given: (hf : StrictAnti f) (hg : Antitone g)
  proof: fun _ _ h => mul_lt_mul_of_lt_of_le (hf h) (hg h.le)

中文:
定理 严格递减.mul_antitone'
  条件: (hf : 严格递减 f) (hg : 递减 g)
  证明: fun _ _ h => mul_lt_mul_of_lt_of_le (hf h) (hg h.le)

Depends on / 依赖: h.le, mul_lt_mul_of_lt_of_le
-/
theorem StrictAnti.mul_antitone' (hf : StrictAnti f) (hg : Antitone g) :
    StrictAnti fun x => f x * g x :=
  fun _ _ h => mul_lt_mul_of_lt_of_le (hf h) (hg h.le)

/-- The product of a strictly antitone function and an antitone function is strictly antitone. -/
@[to_additive add_antitone /-- The sum of a strictly antitone function and an antitone function is
strictly antitone. -/]
/--
theorem `StrictAntiOn.mul_antitone'` / 定理 `StrictAntiOn.mul_antitone'`

English:
theorem StrictAntiOn.mul_antitone'
  given: (hf : StrictAntiOn f s) (hg : AntitoneOn g s)
  proof: fun _ hx _ hy h => mul_lt_mul_of_lt_of_le (hf hx hy h) (hg hx hy h.le)

@[to_additive (attr := simp) cmp_add_left]

中文:
定理 StrictAntiOn.mul_antitone'
  条件: (hf : StrictAntiOn f s) (hg : AntitoneOn g s)
  证明: fun _ hx _ hy h => mul_lt_mul_of_lt_of_le (hf hx hy h) (hg hx hy h.le)

@[to_additive (attr := simp) cmp_add_left]

Depends on / 依赖: h.le, mul_lt_mul_of_lt_of_le
-/
theorem StrictAntiOn.mul_antitone' (hf : StrictAntiOn f s) (hg : AntitoneOn g s) :
    StrictAntiOn (fun x => f x * g x) s :=
  fun _ hx _ hy h => mul_lt_mul_of_lt_of_le (hf hx hy h) (hg hx hy h.le)

@[to_additive (attr := simp) cmp_add_left]
/--
theorem `cmp_mul_left'` / 定理 `cmp_mul_left'`

English:
theorem cmp_mul_left'
  statement: {α : Type*} [Mul α] [LinearOrder α] [MulLeftStrictMono α]
  proof: (strictMono_id.const_mul' a).cmp_map_eq b c

@[to_additive (attr := simp) cmp_add_right]

中文:
定理 cmp_mul_left'
  结论: {α : 类型} [乘法 α] [线性序 α] [MulLeftStrictMono α]
  证明: (strictMono_id.const_mul' a).cmp_map_eq b c

@[to_additive (attr := simp) cmp_add_right]

Depends on / 依赖: cmp_map_eq, const_mul, strictMono_id, strictMono_id.const_mul
-/
theorem cmp_mul_left' {α : Type*} [Mul α] [LinearOrder α] [MulLeftStrictMono α]
    (a b c : α) :
    cmp (a * b) (a * c) = cmp b c :=
  (strictMono_id.const_mul' a).cmp_map_eq b c

@[to_additive (attr := simp) cmp_add_right]
/--
theorem `cmp_mul_right'` / 定理 `cmp_mul_right'`

English:
theorem cmp_mul_right'
  statement: {α : Type*} [Mul α] [LinearOrder α]
  proof: (strictMono_id.mul_const' c).cmp_map_eq a b

中文:
定理 cmp_mul_right'
  结论: {α : 类型} [乘法 α] [线性序 α]
  证明: (strictMono_id.mul_const' c).cmp_map_eq a b

Depends on / 依赖: cmp_map_eq, mul_const, strictMono_id, strictMono_id.mul_const
-/
theorem cmp_mul_right' {α : Type*} [Mul α] [LinearOrder α]
    [MulRightStrictMono α] (a b c : α) :
    cmp (a * c) (b * c) = cmp a b :=
  (strictMono_id.mul_const' c).cmp_map_eq a b

end Mono

/-- An element `a : α` is `MulLECancellable` if `x ↦ a * x` is order-reflecting.
We will make a separate version of many lemmas that require `[MulLeftReflectLE α]` with
`MulLECancellable` assumptions instead. These lemmas can then be instantiated to specific types,
like `ENNReal`, where we can replace the assumption `AddLECancellable x` by `x ≠ ∞`.
-/
@[to_additive
/-- An element `a : α` is `AddLECancellable` if `x ↦ a + x` is order-reflecting.
We will make a separate version of many lemmas that require `[MulLeftReflectLE α]` with
`AddLECancellable` assumptions instead. These lemmas can then be instantiated to specific types,
like `ENNReal`, where we can replace the assumption `AddLECancellable x` by `x ≠ ∞`. -/]
/--
Definition of `MulLECancellable` / `MulLECancellable` 的定义

English:
definition MulLECancellable
  signature: [Mul α] [LE α] (a : α)
  body: forall ⦃b c⦄, a * b <= a * c -> b <= c

@[to_additive]

中文:
定义 MulLECancellable
  签名: [乘法 α] [LE α] (a : α)
  定义体: forall ⦃b c⦄, a * b <= a * c -> b <= c

@[to_additive]
-/
def MulLECancellable [Mul α] [LE α] (a : α) : Prop :=
  forall ⦃b c⦄, a * b <= a * c -> b <= c

@[to_additive]
/--
theorem `Contravariant.MulLECancellable` / 定理 `Contravariant.MulLECancellable`

English:
theorem Contravariant.MulLECancellable
  statement: [Mul α] [LE α] [MulLeftReflectLE α]
  proof: fun _ _ => le_of_mul_le_mul_left'

@[to_additive (attr := simp)]

中文:
定理 Contravariant.MulLECancellable
  结论: [乘法 α] [LE α] [MulLeftReflectLE α]
  证明: fun _ _ => le_of_mul_le_mul_left'

@[to_additive (attr := simp)]

Depends on / 依赖: le_of_mul_le_mul_left
-/
theorem Contravariant.MulLECancellable [Mul α] [LE α] [MulLeftReflectLE α]
    {a : α} :
    MulLECancellable a :=
  fun _ _ => le_of_mul_le_mul_left'

@[to_additive (attr := simp)]
/--
theorem `mulLECancellable_one` / 定理 `mulLECancellable_one`

English:
theorem mulLECancellable_one
  given: [MulOneClass α] [LE α]
  statement: MulLECancellable (1 : α)
  proof: fun a b => by
  simpa only [one_mul] using id

中文:
定理 mulLECancellable_one
  条件: [MulOne类 α] [LE α]
  结论: MulLECancellable (1 : α)
  证明: fun a b => by
  simpa only [one_mul] using id

Depends on / 依赖: one_mul
-/
theorem mulLECancellable_one [MulOneClass α] [LE α] : MulLECancellable (1 : α) := fun a b => by
  simpa only [one_mul] using id

namespace MulLECancellable

@[to_additive]
/--
theorem `Injective` / 定理 `Injective`

English:
theorem Injective
  given: [Mul α] [PartialOrder α] {a : α} (ha : MulLECancellable a)
  proof: fun _ _ h => le_antisymm (ha h.le) (ha h.ge)

@[to_additive]

中文:
定理 单射
  条件: [乘法 α] [偏序 α] {a : α} (ha : MulLECancellable a)
  证明: fun _ _ h => le_antisymm (ha h.le) (ha h.ge)

@[to_additive]
-/
protected theorem Injective [Mul α] [PartialOrder α] {a : α} (ha : MulLECancellable a) :
    Injective (a * ·) :=
  fun _ _ h => le_antisymm (ha h.le) (ha h.ge)

@[to_additive]
/--
theorem `isLeftRegular` / 定理 `isLeftRegular`

English:
theorem isLeftRegular
  statement: [Mul α] [PartialOrder α] {a : α}
  proof: ha.Injective

@[to_additive]

中文:
定理 isLeftRegular
  结论: [乘法 α] [偏序 α] {a : α}
  证明: ha.Injective

@[to_additive]
-/
protected theorem isLeftRegular [Mul α] [PartialOrder α] {a : α}
    (ha : MulLECancellable a) : IsLeftRegular a :=
  ha.Injective

@[to_additive]
/--
theorem `inj` / 定理 `inj`

English:
theorem inj
  given: [Mul α] [PartialOrder α] {a b c : α} (ha : MulLECancellable a)
  proof: ha.Injective.eq_iff

@[to_additive]

中文:
定理 inj
  条件: [乘法 α] [偏序 α] {a b c : α} (ha : MulLECancellable a)
  证明: ha.Injective.eq_iff

@[to_additive]
-/
protected theorem inj [Mul α] [PartialOrder α] {a b c : α} (ha : MulLECancellable a) :
    a * b = a * c ↔ b = c :=
  ha.Injective.eq_iff

@[to_additive]
/--
theorem `injective_left` / 定理 `injective_left`

English:
theorem injective_left
  statement: [Mul α] [IsMulCommutative α] [PartialOrder α] {a : α}
  proof: fun b c h => ha.Injective by dsimp; rwa [mul_comm' a, mul_comm' a]

@[to_additive]

中文:
定理 injective_left
  结论: [乘法 α] [是MulCommutative α] [偏序 α] {a : α}
  证明: fun b c h => ha.Injective by dsimp; rwa [mul_comm' a, mul_comm' a]

@[to_additive]
-/
protected theorem injective_left [Mul α] [IsMulCommutative α] [PartialOrder α] {a : α}
    (ha : MulLECancellable a) : Injective (· * a) :=
fun b c h => ha.Injective by dsimp; rwa [mul_comm' a, mul_comm' a]

@[to_additive]
/--
theorem `inj_left` / 定理 `inj_left`

English:
theorem inj_left
  statement: [Mul α] [IsMulCommutative α] [PartialOrder α] {a b c : α}
  proof: hc.injective_left.eq_iff

中文:
定理 inj_left
  结论: [乘法 α] [是MulCommutative α] [偏序 α] {a b c : α}
  证明: hc.injective_left.eq_iff
-/
protected theorem inj_left [Mul α] [IsMulCommutative α] [PartialOrder α] {a b c : α}
    (hc : MulLECancellable c) : a * c = b * c ↔ a = b :=
  hc.injective_left.eq_iff

variable [LE α]

@[to_additive]
/--
theorem `mul_le_mul_iff_left` / 定理 `mul_le_mul_iff_left`

English:
theorem mul_le_mul_iff_left
  statement: [Mul α] [MulLeftMono α] {a b c : α}
  proof: ⟨fun h => ha h, fun h => mul_le_mul_right h a⟩

@[to_additive]

中文:
定理 mul_le_mul_iff_left
  结论: [乘法 α] [MulLeftMono α] {a b c : α}
  证明: ⟨fun h => ha h, fun h => mul_le_mul_right h a⟩

@[to_additive]
-/
protected theorem mul_le_mul_iff_left [Mul α] [MulLeftMono α] {a b c : α}
    (ha : MulLECancellable a) : a * b <= a * c ↔ b <= c :=
  ⟨fun h => ha h, fun h => mul_le_mul_right h a⟩

@[to_additive]
/--
theorem `mul_le_mul_iff_right` / 定理 `mul_le_mul_iff_right`

English:
theorem mul_le_mul_iff_right
  statement: [Mul α] [IsMulCommutative α] [MulLeftMono α] {a b c : α}
  proof: by
  rw [mul_comm' b]; rw [mul_comm' c]; rw [ha.mul_le_mul_iff_left]

@[to_additive]

中文:
定理 mul_le_mul_iff_right
  结论: [乘法 α] [是MulCommutative α] [MulLeftMono α] {a b c : α}
  证明: by
  rw [mul_comm' b]; rw [mul_comm' c]; rw [ha.mul_le_mul_iff_left]

@[to_additive]
-/
protected theorem mul_le_mul_iff_right [Mul α] [IsMulCommutative α] [MulLeftMono α] {a b c : α}
    (ha : MulLECancellable a) : b * a <= c * a ↔ b <= c := by
  rw [mul_comm' b]; rw [mul_comm' c]; rw [ha.mul_le_mul_iff_left]

@[to_additive]
/--
theorem `le_mul_iff_one_le_right` / 定理 `le_mul_iff_one_le_right`

English:
theorem le_mul_iff_one_le_right
  statement: [MulOneClass α] [MulLeftMono α]
  proof: Iff.trans (by rw [mul_one]) ha.mul_le_mul_iff_left

@[to_additive]

中文:
定理 le_mul_iff_one_le_right
  结论: [MulOne类 α] [MulLeftMono α]
  证明: Iff.trans (by rw [mul_one]) ha.mul_le_mul_iff_left

@[to_additive]
-/
protected theorem le_mul_iff_one_le_right [MulOneClass α] [MulLeftMono α]
    {a b : α} (ha : MulLECancellable a) :
    a <= a * b ↔ 1 <= b :=
  Iff.trans (by rw [mul_one]) ha.mul_le_mul_iff_left

@[to_additive]
/--
theorem `mul_le_iff_le_one_right` / 定理 `mul_le_iff_le_one_right`

English:
theorem mul_le_iff_le_one_right
  statement: [MulOneClass α] [MulLeftMono α]
  proof: Iff.trans (by rw [mul_one]) ha.mul_le_mul_iff_left

@[to_additive]

中文:
定理 mul_le_iff_le_one_right
  结论: [MulOne类 α] [MulLeftMono α]
  证明: Iff.trans (by rw [mul_one]) ha.mul_le_mul_iff_left

@[to_additive]
-/
protected theorem mul_le_iff_le_one_right [MulOneClass α] [MulLeftMono α]
    {a b : α} (ha : MulLECancellable a) :
    a * b <= a ↔ b <= 1 :=
  Iff.trans (by rw [mul_one]) ha.mul_le_mul_iff_left

@[to_additive]
/--
theorem `le_mul_iff_one_le_left` / 定理 `le_mul_iff_one_le_left`

English:
theorem le_mul_iff_one_le_left
  statement: [MulOneClass α] [IsMulCommutative α] [MulLeftMono α]
  proof: by
  rw [mul_comm']; rw [ha.le_mul_iff_one_le_right]

@[to_additive]

中文:
定理 le_mul_iff_one_le_left
  结论: [MulOne类 α] [是MulCommutative α] [MulLeftMono α]
  证明: by
  rw [mul_comm']; rw [ha.le_mul_iff_one_le_right]

@[to_additive]
-/
protected theorem le_mul_iff_one_le_left [MulOneClass α] [IsMulCommutative α] [MulLeftMono α]
    {a b : α} (ha : MulLECancellable a) : a <= b * a ↔ 1 <= b := by
  rw [mul_comm']; rw [ha.le_mul_iff_one_le_right]

@[to_additive]
/--
theorem `mul_le_iff_le_one_left` / 定理 `mul_le_iff_le_one_left`

English:
theorem mul_le_iff_le_one_left
  statement: [MulOneClass α] [IsMulCommutative α] [MulLeftMono α]
  proof: by
  rw [mul_comm']; rw [ha.mul_le_iff_le_one_right]

中文:
定理 mul_le_iff_le_one_left
  结论: [MulOne类 α] [是MulCommutative α] [MulLeftMono α]
  证明: by
  rw [mul_comm']; rw [ha.mul_le_iff_le_one_right]
-/
protected theorem mul_le_iff_le_one_left [MulOneClass α] [IsMulCommutative α] [MulLeftMono α]
    {a b : α} (ha : MulLECancellable a) : b * a <= a ↔ b <= 1 := by
  rw [mul_comm']; rw [ha.mul_le_iff_le_one_right]

/--
lemma `mul` / 引理 `mul`

English:
lemma mul
  statement: [Semigroup α] {a b : α} (ha : MulLECancellable a)
  proof: fun c d hcd => hb ha by rwa [← mul_assoc, ← mul_assoc]

中文:
引理 mul
  结论: [半群 α] {a b : α} (ha : MulLECancellable a)
  证明: fun c d hcd => hb ha by rwa [← mul_assoc, ← mul_assoc]
-/
@[to_additive] lemma mul [Semigroup α] {a b : α} (ha : MulLECancellable a)
    (hb : MulLECancellable b) : MulLECancellable (a * b) :=
fun c d hcd => hb ha by rwa [← mul_assoc, ← mul_assoc]

/--
lemma `of_mul_right` / 引理 `of_mul_right`

English:
lemma of_mul_right
  statement: [Semigroup α] [MulLeftMono α] {a b : α}
  proof: fun c d hcd => h by rw [mul_assoc, mul_assoc]; exact mul_le_mul_right hcd _

中文:
引理 of_mul_right
  结论: [半群 α] [MulLeftMono α] {a b : α}
  证明: fun c d hcd => h by rw [mul_assoc, mul_assoc]; exact mul_le_mul_right hcd _
-/
@[to_additive] lemma of_mul_right [Semigroup α] [MulLeftMono α] {a b : α}
    (h : MulLECancellable (a * b)) : MulLECancellable b :=
fun c d hcd => h by rw [mul_assoc, mul_assoc]; exact mul_le_mul_right hcd _

/--
lemma `of_mul_left` / 引理 `of_mul_left`

English:
lemma of_mul_left
  statement: [CommSemigroup α] [MulLeftMono α] {a b : α}
  proof: (mul_comm a b ▸ h).of_mul_right

中文:
引理 of_mul_left
  结论: [交换半群 α] [MulLeftMono α] {a b : α}
  证明: (mul_comm a b ▸ h).of_mul_right
-/
@[to_additive] lemma of_mul_left [CommSemigroup α] [MulLeftMono α] {a b : α}
    (h : MulLECancellable (a * b)) : MulLECancellable a := (mul_comm a b ▸ h).of_mul_right

end MulLECancellable

@[to_additive (attr := simp)]
/--
lemma `mulLECancellable_mul` / 引理 `mulLECancellable_mul`

English:
lemma mulLECancellable_mul
  given: [LE α] [CommSemigroup α] [MulLeftMono α] {a b : α}
  proof: ⟨fun h => ⟨h.of_mul_left, h.of_mul_right⟩, fun h => h.1.mul h.2⟩

中文:
引理 mulLECancellable_mul
  条件: [LE α] [交换半群 α] [MulLeftMono α] {a b : α}
  证明: ⟨fun h => ⟨h.of_mul_left, h.of_mul_right⟩, fun h => h.1.mul h.2⟩

Depends on / 依赖: h.of_mul_left, h.of_mul_right, of_mul_left, of_mul_right
-/
lemma mulLECancellable_mul [LE α] [CommSemigroup α] [MulLeftMono α] {a b : α} :
    MulLECancellable (a * b) ↔ MulLECancellable a ∧ MulLECancellable b :=
  ⟨fun h => ⟨h.of_mul_left, h.of_mul_right⟩, fun h => h.1.mul h.2⟩
