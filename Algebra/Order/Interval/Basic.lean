/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Canonical
public import Mathlib.Order.Interval.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Interval arithmetic

This file defines arithmetic operations on intervals and prove their correctness. Note that this is
full precision operations. The essentials of float operations can be found
in `Data.FP.Basic`. We have not yet integrated these with the rest of the library.
-/

@[expose] public section


open Function Set

open scoped Pointwise

universe u

variable {ι α : Type*}

/-! ### One/zero -/


section One

section Preorder

variable [Preorder α] [One α]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (NonemptyInterval α)
  body: ⟨NonemptyInterval.pure 1⟩

@[to_additive]

中文:
实例 :
  签名: 幺 (Nonempty整数erval α)
  定义体: ⟨NonemptyInterval.pure 1⟩

@[to_additive]

Depends on / 依赖: NonemptyInterval, NonemptyInterval.pure
-/
instance : One (NonemptyInterval α) :=
  ⟨NonemptyInterval.pure 1⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (Interval α)
  body: ⟨(1 : NonemptyInterval α)⟩

中文:
实例 :
  签名: 幺 (区间 α)
  定义体: ⟨(1 : NonemptyInterval α)⟩

Depends on / 依赖: NonemptyInterval
-/
instance : One (Interval α) :=
  ⟨(1 : NonemptyInterval α)⟩

namespace NonemptyInterval

@[to_additive (attr := simp) toProd_zero]
/--
theorem `toProd_one` / 定理 `toProd_one`

English:
theorem toProd_one
  statement: (1 : NonemptyInterval α).toProd = 1
  proof: rfl

@[to_additive]

中文:
定理 toProd_one
  结论: (1 : Nonempty整数erval α).toProd = 1
  证明: rfl

@[to_additive]
-/
theorem toProd_one : (1 : NonemptyInterval α).toProd = 1 :=
  rfl

@[to_additive]
/--
theorem `fst_one` / 定理 `fst_one`

English:
theorem fst_one
  statement: (1 : NonemptyInterval α).fst = 1
  proof: rfl

@[to_additive]

中文:
定理 fst_one
  结论: (1 : Nonempty整数erval α).fst = 1
  证明: rfl

@[to_additive]
-/
theorem fst_one : (1 : NonemptyInterval α).fst = 1 :=
  rfl

@[to_additive]
/--
theorem `snd_one` / 定理 `snd_one`

English:
theorem snd_one
  statement: (1 : NonemptyInterval α).snd = 1
  proof: rfl

@[to_additive (attr := push_cast, simp)]

中文:
定理 snd_one
  结论: (1 : Nonempty整数erval α).snd = 1
  证明: rfl

@[to_additive (attr := push_cast, simp)]
-/
theorem snd_one : (1 : NonemptyInterval α).snd = 1 :=
  rfl

@[to_additive (attr := push_cast, simp)]
/--
theorem `coe_one_interval` / 定理 `coe_one_interval`

English:
theorem coe_one_interval
  statement: ((1 : NonemptyInterval α) : Interval α) = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_one_interval
  结论: ((1 : Nonempty整数erval α) : 区间 α) = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_one_interval : ((1 : NonemptyInterval α) : Interval α) = 1 :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `pure_one` / 定理 `pure_one`

English:
theorem pure_one
  statement: pure (1 : α) = 1
  proof: rfl

中文:
定理 pure_one
  结论: pure (1 : α) = 1
  证明: rfl
-/
theorem pure_one : pure (1 : α) = 1 :=
  rfl

end NonemptyInterval

namespace Interval

@[to_additive (attr := simp)]
/--
theorem `pure_one` / 定理 `pure_one`

English:
theorem pure_one
  statement: pure (1 : α) = 1
  proof: rfl

中文:
定理 pure_one
  结论: pure (1 : α) = 1
  证明: rfl
-/
theorem pure_one : pure (1 : α) = 1 :=
  rfl

/--
lemma `one_ne_bot` / 引理 `one_ne_bot`

English:
lemma one_ne_bot
  statement: (1 : Interval α) != ⊥
  proof: pure_ne_bot

中文:
引理 one_ne_bot
  结论: (1 : 区间 α) != ⊥
  证明: pure_ne_bot
-/
@[to_additive (attr := simp)] lemma one_ne_bot : (1 : Interval α) != ⊥ := pure_ne_bot

/--
lemma `bot_ne_one` / 引理 `bot_ne_one`

English:
lemma bot_ne_one
  statement: (⊥ : Interval α) != 1
  proof: bot_ne_pure

中文:
引理 bot_ne_one
  结论: (⊥ : 区间 α) != 1
  证明: bot_ne_pure
-/
@[to_additive (attr := simp)] lemma bot_ne_one : (⊥ : Interval α) != 1 := bot_ne_pure

end Interval

end Preorder

section PartialOrder

variable [PartialOrder α] [One α]

namespace NonemptyInterval

@[to_additive (attr := simp)]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : NonemptyInterval α) : Set α) = 1
  proof: coe_pure _

@[to_additive]

中文:
定理 coe_one
  结论: ((1 : Nonempty整数erval α) : 集合 α) = 1
  证明: coe_pure _

@[to_additive]

Depends on / 依赖: coe_pure
-/
theorem coe_one : ((1 : NonemptyInterval α) : Set α) = 1 :=
  coe_pure _

@[to_additive]
/--
theorem `one_mem_one` / 定理 `one_mem_one`

English:
theorem one_mem_one
  statement: (1 : α) in (1 : NonemptyInterval α)
  proof: ⟨le_rfl, le_rfl⟩

中文:
定理 one_mem_one
  结论: (1 : α) in (1 : Nonempty整数erval α)
  证明: ⟨le_rfl, le_rfl⟩

Depends on / 依赖: le_rfl
-/
theorem one_mem_one : (1 : α) in (1 : NonemptyInterval α) :=
  ⟨le_rfl, le_rfl⟩

end NonemptyInterval

namespace Interval

@[to_additive (attr := simp)]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : Interval α) : Set α) = 1
  proof: Icc_self _

@[to_additive]

中文:
定理 coe_one
  结论: ((1 : 区间 α) : 集合 α) = 1
  证明: Icc_self _

@[to_additive]

Depends on / 依赖: Icc_self
-/
theorem coe_one : ((1 : Interval α) : Set α) = 1 :=
  Icc_self _

@[to_additive]
/--
theorem `one_mem_one` / 定理 `one_mem_one`

English:
theorem one_mem_one
  statement: (1 : α) in (1 : Interval α)
  proof: ⟨le_rfl, le_rfl⟩

中文:
定理 one_mem_one
  结论: (1 : α) in (1 : 区间 α)
  证明: ⟨le_rfl, le_rfl⟩

Depends on / 依赖: le_rfl
-/
theorem one_mem_one : (1 : α) in (1 : Interval α) :=
  ⟨le_rfl, le_rfl⟩

end Interval

end PartialOrder

end One

/-!
### Addition/multiplication

Note that this multiplication does not apply to `ℚ` or `ℝ`.
-/


section Mul

variable [Preorder α] [Mul α] [MulLeftMono α] [MulRightMono α]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (NonemptyInterval α)
  body: ⟨fun s t => ⟨s.toProd * t.toProd, mul_le_mul' s.fst_le_snd t.fst_le_snd⟩⟩

@[to_additive]

中文:
实例 :
  签名: 乘法 (Nonempty整数erval α)
  定义体: ⟨fun s t => ⟨s.toProd * t.toProd, mul_le_mul' s.fst_le_snd t.fst_le_snd⟩⟩

@[to_additive]

Depends on / 依赖: fst_le_snd, mul_le_mul, s.fst_le_snd, s.toProd, t.fst_le_snd, t.toProd, toProd
-/
instance : Mul (NonemptyInterval α) :=
  ⟨fun s t => ⟨s.toProd * t.toProd, mul_le_mul' s.fst_le_snd t.fst_le_snd⟩⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (Interval α)
  body: ⟨WithBot.map₂ (· * ·)⟩

中文:
实例 :
  签名: 乘法 (区间 α)
  定义体: ⟨WithBot.map₂ (· * ·)⟩

Depends on / 依赖: WithBot, WithBot.map
-/
instance : Mul (Interval α) :=
  ⟨WithBot.map₂ (· * ·)⟩

namespace NonemptyInterval

variable (s t : NonemptyInterval α) (a b : α)

@[to_additive (attr := simp) toProd_add]
/--
theorem `toProd_mul` / 定理 `toProd_mul`

English:
theorem toProd_mul
  statement: (s * t).toProd = s.toProd * t.toProd
  proof: rfl

@[to_additive]

中文:
定理 toProd_mul
  结论: (s * t).toProd = s.toProd * t.toProd
  证明: rfl

@[to_additive]
-/
theorem toProd_mul : (s * t).toProd = s.toProd * t.toProd :=
  rfl

@[to_additive]
/--
theorem `fst_mul` / 定理 `fst_mul`

English:
theorem fst_mul
  statement: (s * t).fst = s.fst * t.fst
  proof: rfl

@[to_additive]

中文:
定理 fst_mul
  结论: (s * t).fst = s.fst * t.fst
  证明: rfl

@[to_additive]
-/
theorem fst_mul : (s * t).fst = s.fst * t.fst :=
  rfl

@[to_additive]
/--
theorem `snd_mul` / 定理 `snd_mul`

English:
theorem snd_mul
  statement: (s * t).snd = s.snd * t.snd
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 snd_mul
  结论: (s * t).snd = s.snd * t.snd
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem snd_mul : (s * t).snd = s.snd * t.snd :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `coe_mul_interval` / 定理 `coe_mul_interval`

English:
theorem coe_mul_interval
  statement: (↑(s * t) : Interval α) = s * t
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_mul_interval
  结论: (↑(s * t) : 区间 α) = s * t
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_mul_interval : (↑(s * t) : Interval α) = s * t :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `pure_mul_pure` / 定理 `pure_mul_pure`

English:
theorem pure_mul_pure
  statement: pure a * pure b = pure (a * b)
  proof: rfl

中文:
定理 pure_mul_pure
  结论: pure a * pure b = pure (a * b)
  证明: rfl
-/
theorem pure_mul_pure : pure a * pure b = pure (a * b) :=
  rfl

end NonemptyInterval

namespace Interval

variable (s t : Interval α)

@[to_additive (attr := simp)]
/--
theorem `bot_mul` / 定理 `bot_mul`

English:
theorem bot_mul
  statement: ⊥ * t = ⊥
  proof: WithBot.map₂_bot_left _ _

@[to_additive (attr := simp)]

中文:
定理 bot_mul
  结论: ⊥ * t = ⊥
  证明: WithBot.map₂_bot_left _ _

@[to_additive (attr := simp)]

Depends on / 依赖: WithBot, WithBot.map
-/
theorem bot_mul : ⊥ * t = ⊥ :=
  WithBot.map₂_bot_left _ _

@[to_additive (attr := simp)]
/--
theorem `mul_bot` / 定理 `mul_bot`

English:
theorem mul_bot
  statement: s * ⊥ = ⊥
  proof: WithBot.map₂_bot_right _ _

中文:
定理 mul_bot
  结论: s * ⊥ = ⊥
  证明: WithBot.map₂_bot_right _ _

Depends on / 依赖: WithBot, WithBot.map
-/
theorem mul_bot : s * ⊥ = ⊥ :=
  WithBot.map₂_bot_right _ _

-- simp can already prove `add_bot`
attribute [simp] mul_bot

end Interval

end Mul

/-! ### Powers -/

section Pow

variable [Monoid α] [Preorder α]

@[to_additive]
/--
Instance `NonemptyInterval.instPow` / 实例 `NonemptyInterval.instPow`

English:
instance NonemptyInterval.instPow
  signature: [MulLeftMono α] [MulRightMono α]
  body: ⟨fun s n => ⟨s.toProd ^ n, pow_le_pow_left' s.fst_le_snd _⟩⟩

中文:
实例 Nonempty整数erval.instPow
  签名: [MulLeftMono α] [MulRightMono α]
  定义体: ⟨fun s n => ⟨s.toProd ^ n, pow_le_pow_left' s.fst_le_snd _⟩⟩

Depends on / 依赖: fst_le_snd, pow_le_pow_left, s.fst_le_snd, s.toProd, toProd
-/
instance NonemptyInterval.instPow [MulLeftMono α] [MulRightMono α] :
    Pow (NonemptyInterval α) Nat :=
  ⟨fun s n => ⟨s.toProd ^ n, pow_le_pow_left' s.fst_le_snd _⟩⟩

namespace NonemptyInterval

variable [MulLeftMono α] [MulRightMono α]
variable (s : NonemptyInterval α) (a : α) (n : Nat)

@[to_additive (attr := simp) toProd_nsmul]
/--
theorem `toProd_pow` / 定理 `toProd_pow`

English:
theorem toProd_pow
  statement: (s ^ n).toProd = s.toProd ^ n
  proof: rfl

@[to_additive]

中文:
定理 toProd_pow
  结论: (s ^ n).toProd = s.toProd ^ n
  证明: rfl

@[to_additive]
-/
theorem toProd_pow : (s ^ n).toProd = s.toProd ^ n :=
  rfl

@[to_additive]
/--
theorem `fst_pow` / 定理 `fst_pow`

English:
theorem fst_pow
  statement: (s ^ n).fst = s.fst ^ n
  proof: rfl

@[to_additive]

中文:
定理 fst_pow
  结论: (s ^ n).fst = s.fst ^ n
  证明: rfl

@[to_additive]
-/
theorem fst_pow : (s ^ n).fst = s.fst ^ n :=
  rfl

@[to_additive]
/--
theorem `snd_pow` / 定理 `snd_pow`

English:
theorem snd_pow
  statement: (s ^ n).snd = s.snd ^ n
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 snd_pow
  结论: (s ^ n).snd = s.snd ^ n
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem snd_pow : (s ^ n).snd = s.snd ^ n :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `pure_pow` / 定理 `pure_pow`

English:
theorem pure_pow
  statement: pure a ^ n = pure (a ^ n)
  proof: rfl

中文:
定理 pure_pow
  结论: pure a ^ n = pure (a ^ n)
  证明: rfl
-/
theorem pure_pow : pure a ^ n = pure (a ^ n) :=
  rfl

end NonemptyInterval

end Pow

namespace NonemptyInterval

@[to_additive]
/--
Instance `commMonoid` / 实例 `commMonoid`

English:
instance commMonoid
  signature: [CommMonoid α] [Preorder α] [IsOrderedMonoid α]
  body: fast_instance% NonemptyInterval.toProd_injective.commMonoid _ toProd_one toProd_mul toProd_pow

中文:
实例 commMonoid
  签名: [交换幺半群 α] [预序 α] [是Ordered幺半群 α]
  定义体: fast_instance% NonemptyInterval.toProd_injective.commMonoid _ toProd_one toProd_mul toProd_pow

Depends on / 依赖: NonemptyInterval, NonemptyInterval.toProd_injective.commMonoid, commMonoid, fast_instance, toProd_injective, toProd_mul, toProd_one, toProd_pow
-/
instance commMonoid [CommMonoid α] [Preorder α] [IsOrderedMonoid α] :
    CommMonoid (NonemptyInterval α) :=
  fast_instance% NonemptyInterval.toProd_injective.commMonoid _ toProd_one toProd_mul toProd_pow

end NonemptyInterval

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/--
Instance `Interval.mulOneClass` / 实例 `Interval.mulOneClass`

English:
instance Interval.mulOneClass
  signature: [CommMonoid α] [Preorder α] [IsOrderedMonoid α]
  body: (WithBot.map₂_coe_left _ _ _).trans by
      simp_rw [one_mul, ← Function.id_def, WithBot.map_id, id]
  mul_one s :=
(WithBot.map₂_coe_right _ _ _).trans by
      simp_rw [mul_one, ← Function.id_def, WithBot.map_id, id]

@[to_additive]

中文:
实例 区间.mulOneClass
  签名: [交换幺半群 α] [预序 α] [是Ordered幺半群 α]
  定义体: (WithBot.map₂_coe_left _ _ _).trans by
      simp_rw [one_mul, ← Function.id_def, WithBot.map_id, id]
  mul_one s :=
(WithBot.map₂_coe_right _ _ _).trans by
      simp_rw [mul_one, ← Function.id_def, WithBot.map_id, id]

@[to_additive]

Depends on / 依赖: Function, Function.id_def, WithBot, WithBot.map, WithBot.map_id, id_def, map_id, mul_one, one_mul, simp_rw
-/
instance Interval.mulOneClass [CommMonoid α] [Preorder α] [IsOrderedMonoid α] :
    MulOneClass (Interval α) where
  one_mul s :=
(WithBot.map₂_coe_left _ _ _).trans by
      simp_rw [one_mul, ← Function.id_def, WithBot.map_id, id]
  mul_one s :=
(WithBot.map₂_coe_right _ _ _).trans by
      simp_rw [mul_one, ← Function.id_def, WithBot.map_id, id]

@[to_additive]
/--
Instance `Interval.commMonoid` / 实例 `Interval.commMonoid`

English:
instance Interval.commMonoid
  signature: [CommMonoid α] [Preorder α] [IsOrderedMonoid α]
  body: fun _ _ => Option.map₂_comm mul_comm
  mul_assoc := fun _ _ _ => Option.map₂_assoc mul_assoc

中文:
实例 区间.commMonoid
  签名: [交换幺半群 α] [预序 α] [是Ordered幺半群 α]
  定义体: fun _ _ => Option.map₂_comm mul_comm
  mul_assoc := fun _ _ _ => Option.map₂_assoc mul_assoc

Depends on / 依赖: Option.map, mul_comm
-/
instance Interval.commMonoid [CommMonoid α] [Preorder α] [IsOrderedMonoid α] :
    CommMonoid (Interval α) where
  mul_comm := fun _ _ => Option.map₂_comm mul_comm
  mul_assoc := fun _ _ _ => Option.map₂_assoc mul_assoc

namespace NonemptyInterval

@[to_additive]
/--
theorem `coe_pow_interval` / 定理 `coe_pow_interval`

English:
theorem coe_pow_interval
  statement: [CommMonoid α] [Preorder α] [IsOrderedMonoid α]
  proof: map_pow (⟨⟨(↑), coe_one_interval⟩, coe_mul_interval⟩ : NonemptyInterval α ->* Interval α) _ _

中文:
定理 coe_pow_interval
  结论: [交换幺半群 α] [预序 α] [是Ordered幺半群 α]
  证明: map_pow (⟨⟨(↑), coe_one_interval⟩, coe_mul_interval⟩ : NonemptyInterval α ->* Interval α) _ _

Depends on / 依赖: Interval, NonemptyInterval, coe_mul_interval, coe_one_interval, map_pow
-/
theorem coe_pow_interval [CommMonoid α] [Preorder α] [IsOrderedMonoid α]
    (s : NonemptyInterval α) (n : Nat) :
    ↑(s ^ n) = (s : Interval α) ^ n :=
  map_pow (⟨⟨(↑), coe_one_interval⟩, coe_mul_interval⟩ : NonemptyInterval α ->* Interval α) _ _

-- simp can already prove `coe_nsmul_interval`
attribute [simp] coe_pow_interval

end NonemptyInterval

namespace Interval

variable [CommMonoid α] [Preorder α] [IsOrderedMonoid α] (s : Interval α) {n : Nat}

@[to_additive]
/--
theorem `bot_pow` / 定理 `bot_pow`

English:
theorem bot_pow
  statement: forall {n : Nat}, n != 0 -> (⊥ : Interval α) ^ n = ⊥

中文:
定理 bot_pow
  结论: 对任意 {n : 自然数}, n != 0 -> (⊥ : 区间 α) ^ n = ⊥
-/
theorem bot_pow : forall {n : Nat}, n != 0 -> (⊥ : Interval α) ^ n = ⊥
  | 0, h => (h rfl).elim
  | Nat.succ n, _ => mul_bot (⊥ ^ n)

end Interval

/-!
### Semiring structure

When `α` is a canonically `OrderedCommSemiring`, the previous `+` and `*` on `NonemptyInterval α`
form a `CommSemiring`.
-/

section NatCast
variable [Preorder α] [NatCast α]

namespace NonemptyInterval

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatCast (NonemptyInterval α)
  body: pure Nat.cast n

中文:
实例 :
  签名: 自然数嵌入 (Nonempty整数erval α)
  定义体: pure Nat.cast n

Depends on / 依赖: Nat.cast
-/
instance : NatCast (NonemptyInterval α) where
natCast n := pure Nat.cast n

/--
theorem `fst_natCast` / 定理 `fst_natCast`

English:
theorem fst_natCast
  given: (n : Nat)
  statement: (n : NonemptyInterval α).fst = n
  proof: rfl

中文:
定理 fst_natCast
  条件: (n : 自然数)
  结论: (n : Nonempty整数erval α).fst = n
  证明: rfl
-/
theorem fst_natCast (n : Nat) : (n : NonemptyInterval α).fst = n := rfl

/--
theorem `snd_natCast` / 定理 `snd_natCast`

English:
theorem snd_natCast
  given: (n : Nat)
  statement: (n : NonemptyInterval α).snd = n
  proof: rfl

@[simp]

中文:
定理 snd_natCast
  条件: (n : 自然数)
  结论: (n : Nonempty整数erval α).snd = n
  证明: rfl

@[simp]
-/
theorem snd_natCast (n : Nat) : (n : NonemptyInterval α).snd = n := rfl

@[simp]
/--
theorem `pure_natCast` / 定理 `pure_natCast`

English:
theorem pure_natCast
  given: (n : Nat)
  statement: pure (n : α) = n
  proof: rfl

中文:
定理 pure_natCast
  条件: (n : 自然数)
  结论: pure (n : α) = n
  证明: rfl
-/
theorem pure_natCast (n : Nat) : pure (n : α) = n := rfl

end NonemptyInterval

end NatCast

namespace NonemptyInterval

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommSemiring
  signature: α] [PartialOrder α] [CanonicallyOrderedAdd α] :
  body: fast_instance% NonemptyInterval.toProd_injective.commSemiring _
    toProd_zero toProd_one toProd_add toProd_mul (swap toProd_nsmul) toProd_pow (fun _ => rfl)

中文:
实例 [交换半环
  签名: α] [偏序 α] [典范有序加法 α] :
  定义体: fast_instance% NonemptyInterval.toProd_injective.commSemiring _
    toProd_zero toProd_one toProd_add toProd_mul (swap toProd_nsmul) toProd_pow (fun _ => rfl)

Depends on / 依赖: NonemptyInterval, NonemptyInterval.toProd_injective.commSemiring, commSemiring, fast_instance, toProd_add, toProd_injective, toProd_mul, toProd_nsmul, toProd_one, toProd_pow, toProd_zero
-/
instance [CommSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α] :
    CommSemiring (NonemptyInterval α) :=
  fast_instance% NonemptyInterval.toProd_injective.commSemiring _
    toProd_zero toProd_one toProd_add toProd_mul (swap toProd_nsmul) toProd_pow (fun _ => rfl)

end NonemptyInterval

/-!
### Subtraction

Subtraction is defined more generally than division so that it applies to `ℕ` (and `OrderedDiv`
is not a thing and probably should not become one).

However, this means that we can't use `to_additive` in this section.
-/


section Sub

variable [Preorder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] [AddLeftMono α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (NonemptyInterval α)
  body: ⟨fun s t => ⟨(s.fst - t.snd, s.snd - t.fst), tsub_le_tsub s.fst_le_snd t.fst_le_snd⟩⟩

中文:
实例 :
  签名: 减法 (Nonempty整数erval α)
  定义体: ⟨fun s t => ⟨(s.fst - t.snd, s.snd - t.fst), tsub_le_tsub s.fst_le_snd t.fst_le_snd⟩⟩

Depends on / 依赖: fst_le_snd, s.fst, s.fst_le_snd, s.snd, t.fst, t.fst_le_snd, t.snd, tsub_le_tsub
-/
instance : Sub (NonemptyInterval α) :=
  ⟨fun s t => ⟨(s.fst - t.snd, s.snd - t.fst), tsub_le_tsub s.fst_le_snd t.fst_le_snd⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (Interval α)
  body: ⟨WithBot.map₂ Sub.sub⟩

中文:
实例 :
  签名: 减法 (区间 α)
  定义体: ⟨WithBot.map₂ Sub.sub⟩

Depends on / 依赖: Sub.sub, WithBot, WithBot.map
-/
instance : Sub (Interval α) :=
  ⟨WithBot.map₂ Sub.sub⟩

namespace NonemptyInterval

variable (s t : NonemptyInterval α) {a b : α}

@[simp]
/--
theorem `fst_sub` / 定理 `fst_sub`

English:
theorem fst_sub
  statement: (s - t).fst = s.fst - t.snd
  proof: rfl

@[simp]

中文:
定理 fst_sub
  结论: (s - t).fst = s.fst - t.snd
  证明: rfl

@[simp]
-/
theorem fst_sub : (s - t).fst = s.fst - t.snd :=
  rfl

@[simp]
/--
theorem `snd_sub` / 定理 `snd_sub`

English:
theorem snd_sub
  statement: (s - t).snd = s.snd - t.fst
  proof: rfl

@[simp]

中文:
定理 snd_sub
  结论: (s - t).snd = s.snd - t.fst
  证明: rfl

@[simp]
-/
theorem snd_sub : (s - t).snd = s.snd - t.fst :=
  rfl

@[simp]
/--
theorem `coe_sub_interval` / 定理 `coe_sub_interval`

English:
theorem coe_sub_interval
  statement: (↑(s - t) : Interval α) = s - t
  proof: rfl

中文:
定理 coe_sub_interval
  结论: (↑(s - t) : 区间 α) = s - t
  证明: rfl
-/
theorem coe_sub_interval : (↑(s - t) : Interval α) = s - t :=
  rfl

/--
theorem `sub_mem_sub` / 定理 `sub_mem_sub`

English:
theorem sub_mem_sub
  given: (ha : a in s) (hb : b in t)
  statement: a - b in s - t
  proof: ⟨tsub_le_tsub ha.1 hb.2, tsub_le_tsub ha.2 hb.1⟩

@[simp]

中文:
定理 sub_mem_sub
  条件: (ha : a in s) (hb : b in t)
  结论: a - b in s - t
  证明: ⟨tsub_le_tsub ha.1 hb.2, tsub_le_tsub ha.2 hb.1⟩

@[simp]

Depends on / 依赖: tsub_le_tsub
-/
theorem sub_mem_sub (ha : a in s) (hb : b in t) : a - b in s - t :=
  ⟨tsub_le_tsub ha.1 hb.2, tsub_le_tsub ha.2 hb.1⟩

@[simp]
/--
theorem `pure_sub_pure` / 定理 `pure_sub_pure`

English:
theorem pure_sub_pure
  given: (a b : α)
  statement: pure a - pure b = pure (a - b)
  proof: rfl

中文:
定理 pure_sub_pure
  条件: (a b : α)
  结论: pure a - pure b = pure (a - b)
  证明: rfl
-/
theorem pure_sub_pure (a b : α) : pure a - pure b = pure (a - b) :=
  rfl

end NonemptyInterval

namespace Interval

variable (s t : Interval α)

@[simp]
/--
theorem `bot_sub` / 定理 `bot_sub`

English:
theorem bot_sub
  statement: ⊥ - t = ⊥
  proof: WithBot.map₂_bot_left _ _

@[simp]

中文:
定理 bot_sub
  结论: ⊥ - t = ⊥
  证明: WithBot.map₂_bot_left _ _

@[simp]

Depends on / 依赖: WithBot, WithBot.map
-/
theorem bot_sub : ⊥ - t = ⊥ :=
  WithBot.map₂_bot_left _ _

@[simp]
/--
theorem `sub_bot` / 定理 `sub_bot`

English:
theorem sub_bot
  statement: s - ⊥ = ⊥
  proof: WithBot.map₂_bot_right _ _

中文:
定理 sub_bot
  结论: s - ⊥ = ⊥
  证明: WithBot.map₂_bot_right _ _

Depends on / 依赖: WithBot, WithBot.map
-/
theorem sub_bot : s - ⊥ = ⊥ :=
  WithBot.map₂_bot_right _ _

end Interval

end Sub

/-!
### Division in ordered groups

Note that this division does not apply to `ℚ` or `ℝ`.
-/


section Div

variable [Preorder α] [CommGroup α] [MulLeftMono α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Div (NonemptyInterval α)
  body: ⟨fun s t => ⟨(s.fst / t.snd, s.snd / t.fst), div_le_div'' s.fst_le_snd t.fst_le_snd⟩⟩

中文:
实例 :
  签名: 除法 (Nonempty整数erval α)
  定义体: ⟨fun s t => ⟨(s.fst / t.snd, s.snd / t.fst), div_le_div'' s.fst_le_snd t.fst_le_snd⟩⟩

Depends on / 依赖: div_le_div, fst_le_snd, s.fst, s.fst_le_snd, s.snd, t.fst, t.fst_le_snd, t.snd
-/
instance : Div (NonemptyInterval α) :=
  ⟨fun s t => ⟨(s.fst / t.snd, s.snd / t.fst), div_le_div'' s.fst_le_snd t.fst_le_snd⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Div (Interval α)
  body: ⟨WithBot.map₂ (· / ·)⟩

中文:
实例 :
  签名: 除法 (区间 α)
  定义体: ⟨WithBot.map₂ (· / ·)⟩

Depends on / 依赖: WithBot, WithBot.map
-/
instance : Div (Interval α) :=
  ⟨WithBot.map₂ (· / ·)⟩

namespace NonemptyInterval

variable (s t : NonemptyInterval α) (a b : α)

@[simp]
/--
theorem `fst_div` / 定理 `fst_div`

English:
theorem fst_div
  statement: (s / t).fst = s.fst / t.snd
  proof: rfl

@[simp]

中文:
定理 fst_div
  结论: (s / t).fst = s.fst / t.snd
  证明: rfl

@[simp]
-/
theorem fst_div : (s / t).fst = s.fst / t.snd :=
  rfl

@[simp]
/--
theorem `snd_div` / 定理 `snd_div`

English:
theorem snd_div
  statement: (s / t).snd = s.snd / t.fst
  proof: rfl

@[simp]

中文:
定理 snd_div
  结论: (s / t).snd = s.snd / t.fst
  证明: rfl

@[simp]
-/
theorem snd_div : (s / t).snd = s.snd / t.fst :=
  rfl

@[simp]
/--
theorem `coe_div_interval` / 定理 `coe_div_interval`

English:
theorem coe_div_interval
  statement: (↑(s / t) : Interval α) = s / t
  proof: rfl

中文:
定理 coe_div_interval
  结论: (↑(s / t) : 区间 α) = s / t
  证明: rfl
-/
theorem coe_div_interval : (↑(s / t) : Interval α) = s / t :=
  rfl

/--
theorem `div_mem_div` / 定理 `div_mem_div`

English:
theorem div_mem_div
  given: (ha : a in s) (hb : b in t)
  statement: a / b in s / t
  proof: ⟨div_le_div'' ha.1 hb.2, div_le_div'' ha.2 hb.1⟩

@[simp]

中文:
定理 div_mem_div
  条件: (ha : a in s) (hb : b in t)
  结论: a / b in s / t
  证明: ⟨div_le_div'' ha.1 hb.2, div_le_div'' ha.2 hb.1⟩

@[simp]

Depends on / 依赖: div_le_div
-/
theorem div_mem_div (ha : a in s) (hb : b in t) : a / b in s / t :=
  ⟨div_le_div'' ha.1 hb.2, div_le_div'' ha.2 hb.1⟩

@[simp]
/--
theorem `pure_div_pure` / 定理 `pure_div_pure`

English:
theorem pure_div_pure
  statement: pure a / pure b = pure (a / b)
  proof: rfl

中文:
定理 pure_div_pure
  结论: pure a / pure b = pure (a / b)
  证明: rfl
-/
theorem pure_div_pure : pure a / pure b = pure (a / b) :=
  rfl

end NonemptyInterval

namespace Interval

variable (s t : Interval α)

@[simp]
/--
theorem `bot_div` / 定理 `bot_div`

English:
theorem bot_div
  statement: ⊥ / t = ⊥
  proof: WithBot.map₂_bot_left _ _

@[simp]

中文:
定理 bot_div
  结论: ⊥ / t = ⊥
  证明: WithBot.map₂_bot_left _ _

@[simp]

Depends on / 依赖: WithBot, WithBot.map
-/
theorem bot_div : ⊥ / t = ⊥ :=
  WithBot.map₂_bot_left _ _

@[simp]
/--
theorem `div_bot` / 定理 `div_bot`

English:
theorem div_bot
  statement: s / ⊥ = ⊥
  proof: WithBot.map₂_bot_right _ _

中文:
定理 div_bot
  结论: s / ⊥ = ⊥
  证明: WithBot.map₂_bot_right _ _

Depends on / 依赖: WithBot, WithBot.map
-/
theorem div_bot : s / ⊥ = ⊥ :=
  WithBot.map₂_bot_right _ _

end Interval

end Div

/-! ### Negation/inversion -/


section Inv

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv (NonemptyInterval α)
  body: ⟨fun s => ⟨(s.snd⁻¹, s.fst⁻¹), inv_le_inv' s.fst_le_snd⟩⟩

@[to_additive]

中文:
实例 :
  签名: 取逆 (Nonempty整数erval α)
  定义体: ⟨fun s => ⟨(s.snd⁻¹, s.fst⁻¹), inv_le_inv' s.fst_le_snd⟩⟩

@[to_additive]

Depends on / 依赖: fst_le_snd, inv_le_inv, s.fst, s.fst_le_snd, s.snd
-/
instance : Inv (NonemptyInterval α) :=
  ⟨fun s => ⟨(s.snd⁻¹, s.fst⁻¹), inv_le_inv' s.fst_le_snd⟩⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv (Interval α)
  body: ⟨WithBot.map Inv.inv⟩

中文:
实例 :
  签名: 取逆 (区间 α)
  定义体: ⟨WithBot.map Inv.inv⟩

Depends on / 依赖: Inv.inv, WithBot, WithBot.map
-/
instance : Inv (Interval α) :=
  ⟨WithBot.map Inv.inv⟩

namespace NonemptyInterval

variable (s t : NonemptyInterval α) (a : α)

@[to_additive (attr := simp)]
/--
theorem `fst_inv` / 定理 `fst_inv`

English:
theorem fst_inv
  statement: s⁻¹.fst = s.snd⁻¹
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 fst_inv
  结论: s⁻¹.fst = s.snd⁻¹
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem fst_inv : s⁻¹.fst = s.snd⁻¹ :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `snd_inv` / 定理 `snd_inv`

English:
theorem snd_inv
  statement: s⁻¹.snd = s.fst⁻¹
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 snd_inv
  结论: s⁻¹.snd = s.fst⁻¹
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem snd_inv : s⁻¹.snd = s.fst⁻¹ :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `coe_inv_interval` / 定理 `coe_inv_interval`

English:
theorem coe_inv_interval
  statement: (↑(s⁻¹) : Interval α) = (↑s)⁻¹
  proof: rfl

@[to_additive]

中文:
定理 coe_inv_interval
  结论: (↑(s⁻¹) : 区间 α) = (↑s)⁻¹
  证明: rfl

@[to_additive]
-/
theorem coe_inv_interval : (↑(s⁻¹) : Interval α) = (↑s)⁻¹ :=
  rfl

@[to_additive]
/--
theorem `inv_mem_inv` / 定理 `inv_mem_inv`

English:
theorem inv_mem_inv
  given: (ha : a in s)
  statement: a⁻¹ in s⁻¹
  proof: ⟨inv_le_inv' ha.2, inv_le_inv' ha.1⟩

@[to_additive (attr := simp)]

中文:
定理 inv_mem_inv
  条件: (ha : a in s)
  结论: a⁻¹ in s⁻¹
  证明: ⟨inv_le_inv' ha.2, inv_le_inv' ha.1⟩

@[to_additive (attr := simp)]

Depends on / 依赖: inv_le_inv
-/
theorem inv_mem_inv (ha : a in s) : a⁻¹ in s⁻¹ :=
  ⟨inv_le_inv' ha.2, inv_le_inv' ha.1⟩

@[to_additive (attr := simp)]
/--
theorem `inv_pure` / 定理 `inv_pure`

English:
theorem inv_pure
  statement: (pure a)⁻¹ = pure a⁻¹
  proof: rfl

中文:
定理 inv_pure
  结论: (pure a)⁻¹ = pure a⁻¹
  证明: rfl
-/
theorem inv_pure : (pure a)⁻¹ = pure a⁻¹ :=
  rfl

end NonemptyInterval

@[to_additive (attr := simp)]
/--
theorem `Interval.inv_bot` / 定理 `Interval.inv_bot`

English:
theorem Interval.inv_bot
  statement: (⊥ : Interval α)⁻¹ = ⊥
  proof: rfl

中文:
定理 区间.inv_bot
  结论: (⊥ : 区间 α)⁻¹ = ⊥
  证明: rfl
-/
theorem Interval.inv_bot : (⊥ : Interval α)⁻¹ = ⊥ :=
  rfl

end Inv

namespace NonemptyInterval

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {s t : NonemptyInterval α}

@[to_additive]
/--
theorem `mul_eq_one_iff` / 定理 `mul_eq_one_iff`

English:
theorem mul_eq_one_iff
  statement: s * t = 1 ↔ exists a b, s = pure a ∧ t = pure b ∧ a * b = 1
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · rw [NonemptyInterval.ext_iff, Prod.ext_iff] at h
    have := (mul_le_mul_iff_of_ge s.fst_le_snd t.fst_le_snd).1 (h.2.trans h.1.symm).le
    refine ⟨s.fst, t.fst, ?_, ?_, h.1⟩ <;> apply NonemptyInterval.ext <;> dsimp [pure]
    · nth_rw 2 [this.1]
    · nth_rw 2 [this.2]
  · rintro ⟨b, c, rfl, rfl, h⟩
    rw [pure_mul_pure]; rw [h]; rw [pure_one]

中文:
定理 mul_eq_one_iff
  结论: s * t = 1 ↔ 存在 a b, s = pure a ∧ t = pure b ∧ a * b = 1
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · rw [NonemptyInterval.ext_iff, Prod.ext_iff] at h
    have := (mul_le_mul_iff_of_ge s.fst_le_snd t.fst_le_snd).1 (h.2.trans h.1.symm).le
    refine ⟨s.fst, t.fst, ?_, ?_, h.1⟩ <;> apply NonemptyInterval.ext <;> dsimp [pure]
    · nth_rw 2 [this.1]
    · nth_rw 2 [this.2]
  · rintro ⟨b, c, rfl, rfl, h⟩
    rw [pure_mul_pure]; rw [h]; rw [pure_one]
-/
protected theorem mul_eq_one_iff : s * t = 1 ↔ exists a b, s = pure a ∧ t = pure b ∧ a * b = 1 := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [NonemptyInterval.ext_iff, Prod.ext_iff] at h
    have := (mul_le_mul_iff_of_ge s.fst_le_snd t.fst_le_snd).1 (h.2.trans h.1.symm).le
    refine ⟨s.fst, t.fst, ?_, ?_, h.1⟩ <;> apply NonemptyInterval.ext <;> dsimp [pure]
    · nth_rw 2 [this.1]
    · nth_rw 2 [this.2]
  · rintro ⟨b, c, rfl, rfl, h⟩
    rw [pure_mul_pure]; rw [h]; rw [pure_one]

/--
Instance `subtractionCommMonoid` / 实例 `subtractionCommMonoid`

English:
instance subtractionCommMonoid
  signature: {α : Type u}
  body: fun s t => by
    refine NonemptyInterval.ext (Prod.ext ?_ ?_) <;>
    exact sub_eq_add_neg _ _
  neg_neg := fun s => by apply NonemptyInterval.ext; exact neg_neg _
  neg_add_rev := fun s t => by
    refine NonemptyInterval.ext (Prod.ext ?_ ?_) <;>
    exact neg_add_rev _ _
  neg_eq_of_add := fun s t h => by
    obtain ⟨a, b, rfl, rfl, hab⟩ := NonemptyInterval.add_eq_zero_iff.1 h
    rw [neg_pure]; rw [neg_eq_of_add_eq_zero_right hab]
  -- TODO: use a better defeq
  zsmul := zsmulRec

@[to_additive existing NonemptyInterval.subtractionCommMonoid]

中文:
实例 subtractionCommMonoid
  签名: {α : 类型u}
  定义体: fun s t => by
    refine NonemptyInterval.ext (Prod.ext ?_ ?_) <;>
    exact sub_eq_add_neg _ _
  neg_neg := fun s => by apply NonemptyInterval.ext; exact neg_neg _
  neg_add_rev := fun s t => by
    refine NonemptyInterval.ext (Prod.ext ?_ ?_) <;>
    exact neg_add_rev _ _
  neg_eq_of_add := fun s t h => by
    obtain ⟨a, b, rfl, rfl, hab⟩ := NonemptyInterval.add_eq_zero_iff.1 h
    rw [neg_pure]; rw [neg_eq_of_add_eq_zero_right hab]
  -- TODO: use a better defeq
  zsmul := zsmulRec

@[to_additive existing NonemptyInterval.subtractionCommMonoid]

Depends on / 依赖: NonemptyInterval, NonemptyInterval.add_eq_zero_iff, NonemptyInterval.ext, Prod.ext, add_eq_zero_iff, neg_add_rev, neg_eq_of_add, neg_eq_of_add_eq_zero_right, neg_neg, neg_pure, sub_eq_add_neg
-/
instance subtractionCommMonoid {α : Type u}
    [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] :
    SubtractionCommMonoid (NonemptyInterval α) where
  sub_eq_add_neg := fun s t => by
    refine NonemptyInterval.ext (Prod.ext ?_ ?_) <;>
    exact sub_eq_add_neg _ _
  neg_neg := fun s => by apply NonemptyInterval.ext; exact neg_neg _
  neg_add_rev := fun s t => by
    refine NonemptyInterval.ext (Prod.ext ?_ ?_) <;>
    exact neg_add_rev _ _
  neg_eq_of_add := fun s t h => by
    obtain ⟨a, b, rfl, rfl, hab⟩ := NonemptyInterval.add_eq_zero_iff.1 h
    rw [neg_pure]; rw [neg_eq_of_add_eq_zero_right hab]
  -- TODO: use a better defeq
  zsmul := zsmulRec

@[to_additive existing NonemptyInterval.subtractionCommMonoid]
/--
Instance `divisionCommMonoid` / 实例 `divisionCommMonoid`

English:
instance divisionCommMonoid
  signature: : DivisionCommMonoid (NonemptyInterval α) where
  body: fun s t => by
    refine NonemptyInterval.ext (Prod.ext ?_ ?_) <;>
    exact div_eq_mul_inv _ _
  inv_inv := fun s => by apply NonemptyInterval.ext; exact inv_inv _
  mul_inv_rev := fun s t => by
    refine NonemptyInterval.ext (Prod.ext ?_ ?_) <;>
    exact mul_inv_rev _ _
  inv_eq_of_mul := fun s t h => by
    obtain ⟨a, b, rfl, rfl, hab⟩ := NonemptyInterval.mul_eq_one_iff.1 h
    rw [inv_pure]; rw [inv_eq_of_mul_eq_one_right hab]

中文:
实例 divisionCommMonoid
  签名: : DivisionComm幺半群 (Nonempty整数erval α) where
  定义体: fun s t => by
    refine NonemptyInterval.ext (Prod.ext ?_ ?_) <;>
    exact div_eq_mul_inv _ _
  inv_inv := fun s => by apply NonemptyInterval.ext; exact inv_inv _
  mul_inv_rev := fun s t => by
    refine NonemptyInterval.ext (Prod.ext ?_ ?_) <;>
    exact mul_inv_rev _ _
  inv_eq_of_mul := fun s t h => by
    obtain ⟨a, b, rfl, rfl, hab⟩ := NonemptyInterval.mul_eq_one_iff.1 h
    rw [inv_pure]; rw [inv_eq_of_mul_eq_one_right hab]

Depends on / 依赖: NonemptyInterval, NonemptyInterval.ext, NonemptyInterval.mul_eq_one_iff, Prod.ext, div_eq_mul_inv, inv_eq_of_mul, inv_eq_of_mul_eq_one_right, inv_inv, inv_pure, mul_eq_one_iff, mul_inv_rev
-/
instance divisionCommMonoid : DivisionCommMonoid (NonemptyInterval α) where
  div_eq_mul_inv := fun s t => by
    refine NonemptyInterval.ext (Prod.ext ?_ ?_) <;>
    exact div_eq_mul_inv _ _
  inv_inv := fun s => by apply NonemptyInterval.ext; exact inv_inv _
  mul_inv_rev := fun s t => by
    refine NonemptyInterval.ext (Prod.ext ?_ ?_) <;>
    exact mul_inv_rev _ _
  inv_eq_of_mul := fun s t h => by
    obtain ⟨a, b, rfl, rfl, hab⟩ := NonemptyInterval.mul_eq_one_iff.1 h
    rw [inv_pure]; rw [inv_eq_of_mul_eq_one_right hab]

end NonemptyInterval

namespace Interval

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {s t : Interval α}

@[to_additive]
/--
theorem `mul_eq_one_iff` / 定理 `mul_eq_one_iff`

English:
theorem mul_eq_one_iff
  statement: s * t = 1 ↔ exists a b, s = pure a ∧ t = pure b ∧ a * b = 1
  proof: by
  cases s
  · simp
  cases t
  · simp
  · simp_rw [← NonemptyInterval.coe_mul_interval, ← NonemptyInterval.coe_one_interval,
      Interval.coe_inj, NonemptyInterval.coe_eq_pure]
    exact NonemptyInterval.mul_eq_one_iff

中文:
定理 mul_eq_one_iff
  结论: s * t = 1 ↔ 存在 a b, s = pure a ∧ t = pure b ∧ a * b = 1
  证明: by
  cases s
  · simp
  cases t
  · simp
  · simp_rw [← NonemptyInterval.coe_mul_interval, ← NonemptyInterval.coe_one_interval,
      Interval.coe_inj, NonemptyInterval.coe_eq_pure]
    exact NonemptyInterval.mul_eq_one_iff

Depends on / 依赖: AddLeftMono, ExistsAddOfLE, PosMulMono
-/
protected theorem mul_eq_one_iff : s * t = 1 ↔ exists a b, s = pure a ∧ t = pure b ∧ a * b = 1 := by
  cases s
  · simp
  cases t
  · simp
  · simp_rw [← NonemptyInterval.coe_mul_interval, ← NonemptyInterval.coe_one_interval,
      Interval.coe_inj, NonemptyInterval.coe_eq_pure]
    exact NonemptyInterval.mul_eq_one_iff

/--
Instance `subtractionCommMonoid` / 实例 `subtractionCommMonoid`

English:
instance subtractionCommMonoid
  signature: {α : Type u}
  body: by
    rintro (_ | s) (_ | t) <;> first | rfl | exact congr_arg WithBot.some (sub_eq_add_neg _ _)
  neg_neg := by rintro (_ | s) <;> first | rfl | exact congr_arg WithBot.some (neg_neg _)
  neg_add_rev := by
    rintro (_ | s) (_ | t) <;> first | rfl | exact congr_arg WithBot.some (neg_add_rev _ _)
  neg_eq_of_add := by
    rintro (_ | s) (_ | t) h <;>
      first
        | cases h
        | exact congr_arg WithBot.some (neg_eq_of_add_eq_zero_right <| WithBot.coe_injective h)
  -- TODO: use a better defeq
  zsmul := zsmulRec

@[to_additive existing Interval.subtractionCommMonoid]

中文:
实例 subtractionCommMonoid
  签名: {α : 类型u}
  定义体: by
    rintro (_ | s) (_ | t) <;> first | rfl | exact congr_arg WithBot.some (sub_eq_add_neg _ _)
  neg_neg := by rintro (_ | s) <;> first | rfl | exact congr_arg WithBot.some (neg_neg _)
  neg_add_rev := by
    rintro (_ | s) (_ | t) <;> first | rfl | exact congr_arg WithBot.some (neg_add_rev _ _)
  neg_eq_of_add := by
    rintro (_ | s) (_ | t) h <;>
      first
        | cases h
        | exact congr_arg WithBot.some (neg_eq_of_add_eq_zero_right <| WithBot.coe_injective h)
  -- TODO: use a better defeq
  zsmul := zsmulRec

@[to_additive existing Interval.subtractionCommMonoid]

Depends on / 依赖: WithBot, WithBot.coe_injective, WithBot.some, coe_injective, congr_arg, neg_add_rev, neg_eq_of_add, neg_eq_of_add_eq_zero_right, neg_neg, sub_eq_add_neg
-/
instance subtractionCommMonoid {α : Type u}
    [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] :
    SubtractionCommMonoid (Interval α) where
  sub_eq_add_neg := by
    rintro (_ | s) (_ | t) <;> first | rfl | exact congr_arg WithBot.some (sub_eq_add_neg _ _)
  neg_neg := by rintro (_ | s) <;> first | rfl | exact congr_arg WithBot.some (neg_neg _)
  neg_add_rev := by
    rintro (_ | s) (_ | t) <;> first | rfl | exact congr_arg WithBot.some (neg_add_rev _ _)
  neg_eq_of_add := by
    rintro (_ | s) (_ | t) h <;>
      first
        | cases h
        | exact congr_arg WithBot.some (neg_eq_of_add_eq_zero_right <| WithBot.coe_injective h)
  -- TODO: use a better defeq
  zsmul := zsmulRec

@[to_additive existing Interval.subtractionCommMonoid]
/--
Instance `divisionCommMonoid` / 实例 `divisionCommMonoid`

English:
instance divisionCommMonoid
  signature: : DivisionCommMonoid (Interval α) where
  body: by
    rintro (_ | s) (_ | t) <;> first | rfl | exact congr_arg WithBot.some (div_eq_mul_inv _ _)
  inv_inv := by rintro (_ | s) <;> first | rfl | exact congr_arg WithBot.some (inv_inv _)
  mul_inv_rev := by
    rintro (_ | s) (_ | t) <;> first | rfl | exact congr_arg WithBot.some (mul_inv_rev _ _)
  inv_eq_of_mul := by
    rintro (_ | s) (_ | t) h <;>
      first
        | cases h
        | exact congr_arg WithBot.some (inv_eq_of_mul_eq_one_right <| WithBot.coe_injective h)

中文:
实例 divisionCommMonoid
  签名: : DivisionComm幺半群 (区间 α) where
  定义体: by
    rintro (_ | s) (_ | t) <;> first | rfl | exact congr_arg WithBot.some (div_eq_mul_inv _ _)
  inv_inv := by rintro (_ | s) <;> first | rfl | exact congr_arg WithBot.some (inv_inv _)
  mul_inv_rev := by
    rintro (_ | s) (_ | t) <;> first | rfl | exact congr_arg WithBot.some (mul_inv_rev _ _)
  inv_eq_of_mul := by
    rintro (_ | s) (_ | t) h <;>
      first
        | cases h
        | exact congr_arg WithBot.some (inv_eq_of_mul_eq_one_right <| WithBot.coe_injective h)

Depends on / 依赖: WithBot, WithBot.coe_injective, WithBot.some, coe_injective, congr_arg, div_eq_mul_inv, inv_eq_of_mul, inv_eq_of_mul_eq_one_right, inv_inv, mul_inv_rev
-/
instance divisionCommMonoid : DivisionCommMonoid (Interval α) where
  div_eq_mul_inv := by
    rintro (_ | s) (_ | t) <;> first | rfl | exact congr_arg WithBot.some (div_eq_mul_inv _ _)
  inv_inv := by rintro (_ | s) <;> first | rfl | exact congr_arg WithBot.some (inv_inv _)
  mul_inv_rev := by
    rintro (_ | s) (_ | t) <;> first | rfl | exact congr_arg WithBot.some (mul_inv_rev _ _)
  inv_eq_of_mul := by
    rintro (_ | s) (_ | t) h <;>
      first
        | cases h
        | exact congr_arg WithBot.some (inv_eq_of_mul_eq_one_right <| WithBot.coe_injective h)

end Interval

section Length

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]

namespace NonemptyInterval

variable (s t : NonemptyInterval α) (a : α)

/--
Definition of `length` / `length` 的定义

English:
definition length
  signature: : α
  body: s.snd - s.fst

@[simp]

中文:
定义 length
  签名: : α
  定义体: s.snd - s.fst

@[simp]

Depends on / 依赖: s.fst, s.snd
-/
def length : α :=
  s.snd - s.fst

@[simp]
/--
theorem `length_nonneg` / 定理 `length_nonneg`

English:
theorem length_nonneg
  statement: 0 <= s.length
  proof: sub_nonneg_of_le s.fst_le_snd

omit [IsOrderedAddMonoid α] in
@[simp]

中文:
定理 length_nonneg
  结论: 0 <= s.length
  证明: sub_nonneg_of_le s.fst_le_snd

omit [IsOrderedAddMonoid α] in
@[simp]

Depends on / 依赖: fst_le_snd, s.fst_le_snd, sub_nonneg_of_le
-/
theorem length_nonneg : 0 <= s.length :=
  sub_nonneg_of_le s.fst_le_snd

omit [IsOrderedAddMonoid α] in
@[simp]
/--
theorem `length_pure` / 定理 `length_pure`

English:
theorem length_pure
  statement: (pure a).length = 0
  proof: sub_self _

omit [IsOrderedAddMonoid α] in
@[simp]

中文:
定理 length_pure
  结论: (pure a).length = 0
  证明: sub_self _

omit [IsOrderedAddMonoid α] in
@[simp]

Depends on / 依赖: sub_self
-/
theorem length_pure : (pure a).length = 0 :=
  sub_self _

omit [IsOrderedAddMonoid α] in
@[simp]
/--
theorem `length_zero` / 定理 `length_zero`

English:
theorem length_zero
  statement: (0 : NonemptyInterval α).length = 0
  proof: length_pure _

@[simp]

中文:
定理 length_zero
  结论: (0 : Nonempty整数erval α).length = 0
  证明: length_pure _

@[simp]

Depends on / 依赖: length_pure
-/
theorem length_zero : (0 : NonemptyInterval α).length = 0 :=
  length_pure _

@[simp]
/--
theorem `length_neg` / 定理 `length_neg`

English:
theorem length_neg
  statement: (-s).length = s.length
  proof: neg_sub_neg _ _

@[simp]

中文:
定理 length_neg
  结论: (-s).length = s.length
  证明: neg_sub_neg _ _

@[simp]

Depends on / 依赖: neg_sub_neg
-/
theorem length_neg : (-s).length = s.length :=
  neg_sub_neg _ _

@[simp]
/--
theorem `length_add` / 定理 `length_add`

English:
theorem length_add
  statement: (s + t).length = s.length + t.length
  proof: add_sub_add_comm _ _ _ _

@[simp]

中文:
定理 length_add
  结论: (s + t).length = s.length + t.length
  证明: add_sub_add_comm _ _ _ _

@[simp]

Depends on / 依赖: add_sub_add_comm
-/
theorem length_add : (s + t).length = s.length + t.length :=
  add_sub_add_comm _ _ _ _

@[simp]
/--
theorem `length_sub` / 定理 `length_sub`

English:
theorem length_sub
  statement: (s - t).length = s.length + t.length
  proof: by simp [sub_eq_add_neg]

@[simp]

中文:
定理 length_sub
  结论: (s - t).length = s.length + t.length
  证明: by simp [sub_eq_add_neg]

@[simp]

Depends on / 依赖: sub_eq_add_neg
-/
theorem length_sub : (s - t).length = s.length + t.length := by simp [sub_eq_add_neg]

@[simp]
/--
theorem `length_sum` / 定理 `length_sum`

English:
theorem length_sum
  given: (f : ι -> NonemptyInterval α) (s : Finset ι)
  proof: map_sum (⟨⟨length, length_zero⟩, length_add⟩ : NonemptyInterval α ->+ α) _ _

中文:
定理 length_sum
  条件: (f : ι -> Nonempty整数erval α) (s : 有限集 ι)
  证明: map_sum (⟨⟨length, length_zero⟩, length_add⟩ : NonemptyInterval α ->+ α) _ _

Depends on / 依赖: NonemptyInterval, length, length_add, length_zero, map_sum
-/
theorem length_sum (f : ι -> NonemptyInterval α) (s : Finset ι) :
    (∑ i in s, f i).length = ∑ i in s, (f i).length :=
  map_sum (⟨⟨length, length_zero⟩, length_add⟩ : NonemptyInterval α ->+ α) _ _

end NonemptyInterval

namespace Interval

variable (s t : Interval α) (a : α)

/--
Definition of `length` / `length` 的定义

English:
definition length
  signature: : Interval α -> α

中文:
定义 length
  签名: : 区间 α -> α
-/
def length : Interval α -> α
  | ⊥ => 0
  | (s : NonemptyInterval α) => s.length

@[simp]
/--
theorem `length_nonneg` / 定理 `length_nonneg`

English:
theorem length_nonneg
  statement: forall s : Interval α, 0 <= s.length

中文:
定理 length_nonneg
  结论: 对任意 s : 区间 α, 0 <= s.length
-/
theorem length_nonneg : forall s : Interval α, 0 <= s.length
  | ⊥ => le_rfl
  | (s : NonemptyInterval α) => s.length_nonneg

omit [IsOrderedAddMonoid α] in
@[simp]
/--
theorem `length_pure` / 定理 `length_pure`

English:
theorem length_pure
  statement: (pure a).length = 0
  proof: NonemptyInterval.length_pure _

omit [IsOrderedAddMonoid α] in
@[simp]

中文:
定理 length_pure
  结论: (pure a).length = 0
  证明: NonemptyInterval.length_pure _

omit [IsOrderedAddMonoid α] in
@[simp]

Depends on / 依赖: NonemptyInterval, NonemptyInterval.length_pure, length_pure
-/
theorem length_pure : (pure a).length = 0 :=
  NonemptyInterval.length_pure _

omit [IsOrderedAddMonoid α] in
@[simp]
/--
theorem `length_zero` / 定理 `length_zero`

English:
theorem length_zero
  statement: (0 : Interval α).length = 0
  proof: length_pure _

@[simp]

中文:
定理 length_zero
  结论: (0 : 区间 α).length = 0
  证明: length_pure _

@[simp]

Depends on / 依赖: length_pure
-/
theorem length_zero : (0 : Interval α).length = 0 :=
  length_pure _

@[simp]
/--
theorem `length_neg` / 定理 `length_neg`

English:
theorem length_neg
  statement: forall s : Interval α, (-s).length = s.length

中文:
定理 length_neg
  结论: 对任意 s : 区间 α, (-s).length = s.length
-/
theorem length_neg : forall s : Interval α, (-s).length = s.length
  | ⊥ => rfl
  | (s : NonemptyInterval α) => s.length_neg

omit [IsOrderedAddMonoid α] in
@[simp]
/--
theorem `length_bot` / 定理 `length_bot`

English:
theorem length_bot
  statement: (⊥ : Interval α).length = 0
  proof: rfl

中文:
定理 length_bot
  结论: (⊥ : 区间 α).length = 0
  证明: rfl
-/
theorem length_bot : (⊥ : Interval α).length = 0 := rfl

/--
theorem `length_add_le` / 定理 `length_add_le`

English:
theorem length_add_le
  statement: forall s t : Interval α, (s + t).length <= s.length + t.length

中文:
定理 length_add_le
  结论: 对任意 s t : 区间 α, (s + t).length <= s.length + t.length
-/
theorem length_add_le : forall s t : Interval α, (s + t).length <= s.length + t.length
  | ⊥, _ => by simp
  | _, ⊥ => by simp
  | (s : NonemptyInterval α), (t : NonemptyInterval α) => (s.length_add t).le

/--
theorem `length_sub_le` / 定理 `length_sub_le`

English:
theorem length_sub_le
  statement: (s - t).length <= s.length + t.length
  proof: by
  simpa [sub_eq_add_neg] using length_add_le s (-t)

中文:
定理 length_sub_le
  结论: (s - t).length <= s.length + t.length
  证明: by
  simpa [sub_eq_add_neg] using length_add_le s (-t)

Depends on / 依赖: length_add_le, sub_eq_add_neg
-/
theorem length_sub_le : (s - t).length <= s.length + t.length := by
  simpa [sub_eq_add_neg] using length_add_le s (-t)

/--
theorem `length_sum_le` / 定理 `length_sum_le`

English:
theorem length_sum_le
  given: (f : ι -> Interval α) (s : Finset ι)
  proof: Finset.le_sum_of_subadditive _ length_zero.le length_add_le _ _

中文:
定理 length_sum_le
  条件: (f : ι -> 区间 α) (s : 有限集 ι)
  证明: Finset.le_sum_of_subadditive _ length_zero.le length_add_le _ _

Depends on / 依赖: Finset, Finset.le_sum_of_subadditive, le_sum_of_subadditive, length_add_le, length_zero, length_zero.le
-/
theorem length_sum_le (f : ι -> Interval α) (s : Finset ι) :
    (∑ i in s, f i).length <= ∑ i in s, (f i).length :=
  Finset.le_sum_of_subadditive _ length_zero.le length_add_le _ _

end Interval

end Length

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

/-- Extension for the `positivity` tactic: The length of an interval is always nonnegative. -/
@[positivity NonemptyInterval.length _]
meta def evalNonemptyIntervalLength : PositivityExt where
  eval {u α} _ pα? e :=
    match pα? with | none => pure .none | some _ => do
    let ~q(@NonemptyInterval.length _ $ig $ipo $a) := e |
      throwError "not NonemptyInterval.length"
    let _i ← synthInstanceQ q(IsOrderedAddMonoid $α)
    assertInstancesCommute
    return .nonnegative q(NonemptyInterval.length_nonneg $a)

/-- Extension for the `positivity` tactic: The length of an interval is always nonnegative. -/
@[positivity Interval.length _]
meta def evalIntervalLength : PositivityExt where
  eval {u α} _ pα? e :=
    match pα? with | none => pure .none | some _ => do
    let ~q(@Interval.length _ $ig $ipo $a) := e | throwError "not Interval.length"
    let _i ← synthInstanceQ q(IsOrderedAddMonoid $α)
    assumeInstancesCommute
    return .nonnegative q(Interval.length_nonneg $a)

end Mathlib.Meta.Positivity
