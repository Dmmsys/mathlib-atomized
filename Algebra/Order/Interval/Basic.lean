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
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (NonemptyInterval α) :=
  ⟨NonemptyInterval.pure 1⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (Interval α) :=
  ⟨(1 : NonemptyInterval α)⟩

namespace NonemptyInterval

@[to_additive (attr := simp) toProd_zero]
/-
**NonemptyInterval.toProd_one** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：toProd_one : (1 : NonemptyInterval α).toProd = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toProd_one : (1 : NonemptyInterval α).toProd = 1 :=
  rfl

@[to_additive]
/-
**NonemptyInterval.fst_one** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：fst_one : (1 : NonemptyInterval α).fst = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_one : (1 : NonemptyInterval α).fst = 1 :=
  rfl

@[to_additive]
/-
**NonemptyInterval.snd_one** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：snd_one : (1 : NonemptyInterval α).snd = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_one : (1 : NonemptyInterval α).snd = 1 :=
  rfl

@[to_additive (attr := push_cast, simp)]
/-
**NonemptyInterval.coe_one_interval** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`
。
形式化陈述：coe_one_interval : ((1 : NonemptyInterval α) : Interval α) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one_interval : ((1 : NonemptyInterval α) : Interval α) = 1 :=
  rfl

@[to_additive (attr := simp)]
/-
**NonemptyInterval.pure_one** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：pure_one : pure (1 : α) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pure_one : pure (1 : α) = 1 :=
  rfl

end NonemptyInterval

namespace Interval

@[to_additive (attr := simp)]
/-
**Interval.pure_one** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：pure_one : pure (1 : α) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pure_one : pure (1 : α) = 1 :=
  rfl
/-
**Interval.one_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] [inst_1 : One α], 1 ≠ ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Interval.pure_ne_bot`：pure_ne_bot {a : α} : pure a != ⊥
-/
@[to_additive (attr := simp)] lemma one_ne_bot : (1 : Interval α) ≠ ⊥ := pure_ne_bot
/-
**Interval.bot_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] [inst_1 : One α], ⊥ ≠ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Interval.bot_ne_pure`：bot_ne_pure {a : α} : ⊥ != pure a
-/
@[to_additive (attr := simp)] lemma bot_ne_one : (⊥ : Interval α) ≠ 1 := bot_ne_pure

end Interval

end Preorder

section PartialOrder

variable [PartialOrder α] [One α]

namespace NonemptyInterval

@[to_additive (attr := simp)]
/-
**NonemptyInterval.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：coe_one : ((1 : NonemptyInterval α) : Set α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonemptyInterval.coe_pure`：coe_pure (a : α) : (pure a : Set α) = {a}
-/
theorem coe_one : ((1 : NonemptyInterval α) : Set α) = 1 :=
  coe_pure _

@[to_additive]
/-
**NonemptyInterval.one_mem_one** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：one_mem_one : (1 : α) in (1 : NonemptyInterval α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem one_mem_one : (1 : α) ∈ (1 : NonemptyInterval α) :=
  ⟨le_rfl, le_rfl⟩

end NonemptyInterval

namespace Interval

@[to_additive (attr := simp)]
/-
**Interval.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：coe_one : ((1 : Interval α) : Set α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
-/
theorem coe_one : ((1 : Interval α) : Set α) = 1 :=
  Icc_self _

@[to_additive]
/-
**Interval.one_mem_one** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：one_mem_one : (1 : α) in (1 : Interval α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem one_mem_one : (1 : α) ∈ (1 : Interval α) :=
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
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (NonemptyInterval α) :=
  ⟨fun s t => ⟨s.toProd * t.toProd, mul_le_mul' s.fst_le_snd t.fst_le_snd⟩⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (Interval α) :=
  ⟨WithBot.map₂ (· * ·)⟩

namespace NonemptyInterval

variable (s t : NonemptyInterval α) (a b : α)

@[to_additive (attr := simp) toProd_add]
/-
**NonemptyInterval.toProd_mul** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：toProd_mul : (s * t).toProd = s.toProd * t.toProd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toProd_mul : (s * t).toProd = s.toProd * t.toProd :=
  rfl

@[to_additive]
/-
**NonemptyInterval.fst_mul** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：fst_mul : (s * t).fst = s.fst * t.fst
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_mul : (s * t).fst = s.fst * t.fst :=
  rfl

@[to_additive]
/-
**NonemptyInterval.snd_mul** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：snd_mul : (s * t).snd = s.snd * t.snd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_mul : (s * t).snd = s.snd * t.snd :=
  rfl

@[to_additive (attr := simp)]
/-
**NonemptyInterval.coe_mul_interval** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`
。
形式化陈述：coe_mul_interval : (↑(s * t) : Interval α) = s * t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul_interval : (↑(s * t) : Interval α) = s * t :=
  rfl

@[to_additive (attr := simp)]
/-
**NonemptyInterval.pure_mul_pure** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：pure_mul_pure : pure a * pure b = pure (a * b)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pure_mul_pure : pure a * pure b = pure (a * b) :=
  rfl

end NonemptyInterval

namespace Interval

variable (s t : Interval α)

@[to_additive (attr := simp)]
/-
**Interval.bot_mul** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：bot_mul : ⊥ * t = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.map₂_bot_left`：map₂_bot_left (f : α -> β -> γ) (b) : map₂ f ⊥ b 
= ⊥
-/
theorem bot_mul : ⊥ * t = ⊥ :=
  WithBot.map₂_bot_left _ _

@[to_additive (attr := simp)]
/-
**Interval.mul_bot** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：mul_bot : s * ⊥ = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.map₂_bot_right`：map₂_bot_right (f : α -> β -> γ) (a) : map₂ f a 
⊥ = ⊥
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
/-
**NonemptyInterval.instPow** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NonemptyInterval.instPow [MulLeftMono α] [MulRightMono α] : Pow (NonemptyI
nterval α) Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance NonemptyInterval.instPow [MulLeftMono α] [MulRightMono α] :
    Pow (NonemptyInterval α) ℕ :=
  ⟨fun s n => ⟨s.toProd ^ n, pow_le_pow_left' s.fst_le_snd _⟩⟩

namespace NonemptyInterval

variable [MulLeftMono α] [MulRightMono α]
variable (s : NonemptyInterval α) (a : α) (n : ℕ)

@[to_additive (attr := simp) toProd_nsmul]
/-
**NonemptyInterval.toProd_pow** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：toProd_pow : (s ^ n).toProd = s.toProd ^ n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toProd_pow : (s ^ n).toProd = s.toProd ^ n :=
  rfl

@[to_additive]
/-
**NonemptyInterval.fst_pow** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：fst_pow : (s ^ n).fst = s.fst ^ n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_pow : (s ^ n).fst = s.fst ^ n :=
  rfl

@[to_additive]
/-
**NonemptyInterval.snd_pow** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：snd_pow : (s ^ n).snd = s.snd ^ n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_pow : (s ^ n).snd = s.snd ^ n :=
  rfl

@[to_additive (attr := simp)]
/-
**NonemptyInterval.pure_pow** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：pure_pow : pure a ^ n = pure (a ^ n)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pure_pow : pure a ^ n = pure (a ^ n) :=
  rfl

end NonemptyInterval

end Pow

namespace NonemptyInterval

@[to_additive]
/-
**NonemptyInterval.commMonoid** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInterval`。
形式化陈述：commMonoid [CommMonoid α] [Preorder α] [IsOrderedMonoid α] : CommMonoid (N
onemptyInterval α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
instance commMonoid [CommMonoid α] [Preorder α] [IsOrderedMonoid α] :
    CommMonoid (NonemptyInterval α) :=
  fast_instance% NonemptyInterval.toProd_injective.commMonoid _ toProd_one toProd_mul toProd_pow

end NonemptyInterval

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**Interval.mulOneClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Interval.mulOneClass [CommMonoid α] [Preorder α] [IsOrderedMonoid α] : Mul
OneClass (Interval α) where one_mul s
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
instance Interval.mulOneClass [CommMonoid α] [Preorder α] [IsOrderedMonoid α] :
    MulOneClass (Interval α) where
  one_mul s :=
    (WithBot.map₂_coe_left _ _ _).trans <| by
      simp_rw [one_mul, ← Function.id_def, WithBot.map_id, id]
  mul_one s :=
    (WithBot.map₂_coe_right _ _ _).trans <| by
      simp_rw [mul_one, ← Function.id_def, WithBot.map_id, id]

@[to_additive]
/-
**Interval.commMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Interval.commMonoid [CommMonoid α] [Preorder α] [IsOrderedMonoid α] : Comm
Monoid (Interval α) where mul_comm
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Interval.commMonoid [CommMonoid α] [Preorder α] [IsOrderedMonoid α] :
    CommMonoid (Interval α) where
  mul_comm := fun _ _ => Option.map₂_comm mul_comm
  mul_assoc := fun _ _ _ => Option.map₂_assoc mul_assoc

namespace NonemptyInterval

@[to_additive]
/-
**NonemptyInterval.coe_pow_interval** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`
。
形式化陈述：coe_pow_interval [CommMonoid α] [Preorder α] [IsOrderedMonoid α] (s : None
mptyInterval α) (n : Nat) : ↑(s ^ n) = (s : Interval α) ^ n
参数：s : NonemptyInterval α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `NonemptyInterval.coe_one_interval`：coe_one_interval : ((1 : NonemptyInte
rval α) : Interval α) = 1
· 使用定理 `NonemptyInterval.coe_mul_interval`：coe_mul_interval : (↑(s * t) : Interv
al α) = s * t
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem coe_pow_interval [CommMonoid α] [Preorder α] [IsOrderedMonoid α]
    (s : NonemptyInterval α) (n : ℕ) :
    ↑(s ^ n) = (s : Interval α) ^ n :=
  map_pow (⟨⟨(↑), coe_one_interval⟩, coe_mul_interval⟩ : NonemptyInterval α →* Interval α) _ _

-- simp can already prove `coe_nsmul_interval`
attribute [simp] coe_pow_interval

end NonemptyInterval

namespace Interval

variable [CommMonoid α] [Preorder α] [IsOrderedMonoid α] (s : Interval α) {n : ℕ}

@[to_additive]
/-
**Interval.bot_pow** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：∀ {α : Type u_2} [inst : CommMonoid α] [inst_1 : Preorder α] [inst_2 : IsO
rderedMonoid α] {n : ℕ}, n ≠ 0 → ⊥ ^ n = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Interval.mul_bot`：mul_bot : s * ⊥ = ⊥
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem bot_pow : ∀ {n : ℕ}, n ≠ 0 → (⊥ : Interval α) ^ n = ⊥
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

/-
**NonemptyInterval.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NatCast (NonemptyInterval α) where
  natCast n := pure <| Nat.cast n
/-
**NonemptyInterval.fst_natCast** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：fst_natCast (n : Nat) : (n : NonemptyInterval α).fst = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_natCast (n : ℕ) : (n : NonemptyInterval α).fst = n := rfl
/-
**NonemptyInterval.snd_natCast** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：snd_natCast (n : Nat) : (n : NonemptyInterval α).snd = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_natCast (n : ℕ) : (n : NonemptyInterval α).snd = n := rfl

@[simp]
/-
**NonemptyInterval.pure_natCast** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：pure_natCast (n : Nat) : pure (n : α) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pure_natCast (n : ℕ) : pure (n : α) = n := rfl

end NonemptyInterval

end NatCast

namespace NonemptyInterval

/-
**NonemptyInterval.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (NonemptyInterval α) :=
  ⟨fun s t => ⟨(s.fst - t.snd, s.snd - t.fst), tsub_le_tsub s.fst_le_snd t.fst_le_snd⟩⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (Interval α) :=
  ⟨WithBot.map₂ Sub.sub⟩

namespace NonemptyInterval

variable (s t : NonemptyInterval α) {a b : α}

@[simp]
/-
**NonemptyInterval.fst_sub** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：fst_sub : (s - t).fst = s.fst - t.snd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_sub : (s - t).fst = s.fst - t.snd :=
  rfl

@[simp]
/-
**NonemptyInterval.snd_sub** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：snd_sub : (s - t).snd = s.snd - t.fst
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_sub : (s - t).snd = s.snd - t.fst :=
  rfl

@[simp]
/-
**NonemptyInterval.coe_sub_interval** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`
。
形式化陈述：coe_sub_interval : (↑(s - t) : Interval α) = s - t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sub_interval : (↑(s - t) : Interval α) = s - t :=
  rfl
/-
**NonemptyInterval.sub_mem_sub** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：sub_mem_sub (ha : a in s) (hb : b in t) : a - b in s - t
参数：ha : a in s；hb : b in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsub_le_tsub`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : AddCommSemi
group α] [inst_2 : Sub α] [OrderedSub α] {a b c d : α}   [AddLeftMono α], a ≤ b 
→ …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem sub_mem_sub (ha : a ∈ s) (hb : b ∈ t) : a - b ∈ s - t :=
  ⟨tsub_le_tsub ha.1 hb.2, tsub_le_tsub ha.2 hb.1⟩

@[simp]
/-
**NonemptyInterval.pure_sub_pure** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：pure_sub_pure (a b : α) : pure a - pure b = pure (a - b)
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pure_sub_pure (a b : α) : pure a - pure b = pure (a - b) :=
  rfl

end NonemptyInterval

namespace Interval

variable (s t : Interval α)

@[simp]
/-
**Interval.bot_sub** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：bot_sub : ⊥ - t = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.map₂_bot_left`：map₂_bot_left (f : α -> β -> γ) (b) : map₂ f ⊥ b 
= ⊥
-/
theorem bot_sub : ⊥ - t = ⊥ :=
  WithBot.map₂_bot_left _ _

@[simp]
/-
**Interval.sub_bot** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：sub_bot : s - ⊥ = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.map₂_bot_right`：map₂_bot_right (f : α -> β -> γ) (a) : map₂ f a 
⊥ = ⊥
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

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Div (NonemptyInterval α) :=
  ⟨fun s t => ⟨(s.fst / t.snd, s.snd / t.fst), div_le_div'' s.fst_le_snd t.fst_le_snd⟩⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Div (Interval α) :=
  ⟨WithBot.map₂ (· / ·)⟩

namespace NonemptyInterval

variable (s t : NonemptyInterval α) (a b : α)

@[simp]
/-
**NonemptyInterval.fst_div** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：fst_div : (s / t).fst = s.fst / t.snd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_div : (s / t).fst = s.fst / t.snd :=
  rfl

@[simp]
/-
**NonemptyInterval.snd_div** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：snd_div : (s / t).snd = s.snd / t.fst
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_div : (s / t).snd = s.snd / t.fst :=
  rfl

@[simp]
/-
**NonemptyInterval.coe_div_interval** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`
。
形式化陈述：coe_div_interval : (↑(s / t) : Interval α) = s / t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_div_interval : (↑(s / t) : Interval α) = s / t :=
  rfl
/-
**NonemptyInterval.div_mem_div** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：div_mem_div (ha : a in s) (hb : b in t) : a / b in s / t
参数：ha : a in s；hb : b in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `div_le_div''`：div_le_div'' (hab : a <= b) (hcd : c <= d) : a / d <= b / 
c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem div_mem_div (ha : a ∈ s) (hb : b ∈ t) : a / b ∈ s / t :=
  ⟨div_le_div'' ha.1 hb.2, div_le_div'' ha.2 hb.1⟩

@[simp]
/-
**NonemptyInterval.pure_div_pure** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：pure_div_pure : pure a / pure b = pure (a / b)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pure_div_pure : pure a / pure b = pure (a / b) :=
  rfl

end NonemptyInterval

namespace Interval

variable (s t : Interval α)

@[simp]
/-
**Interval.bot_div** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：bot_div : ⊥ / t = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.map₂_bot_left`：map₂_bot_left (f : α -> β -> γ) (b) : map₂ f ⊥ b 
= ⊥
-/
theorem bot_div : ⊥ / t = ⊥ :=
  WithBot.map₂_bot_left _ _

@[simp]
/-
**Interval.div_bot** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：div_bot : s / ⊥ = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.map₂_bot_right`：map₂_bot_right (f : α -> β -> γ) (a) : map₂ f a 
⊥ = ⊥
-/
theorem div_bot : s / ⊥ = ⊥ :=
  WithBot.map₂_bot_right _ _

end Interval

end Div

/-! ### Negation/inversion -/


section Inv

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inv (NonemptyInterval α) :=
  ⟨fun s => ⟨(s.snd⁻¹, s.fst⁻¹), inv_le_inv' s.fst_le_snd⟩⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inv (Interval α) :=
  ⟨WithBot.map Inv.inv⟩

namespace NonemptyInterval

variable (s t : NonemptyInterval α) (a : α)

@[to_additive (attr := simp)]
/-
**NonemptyInterval.fst_inv** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：fst_inv : s⁻¹.fst = s.snd⁻¹
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_inv : s⁻¹.fst = s.snd⁻¹ :=
  rfl

@[to_additive (attr := simp)]
/-
**NonemptyInterval.snd_inv** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：snd_inv : s⁻¹.snd = s.fst⁻¹
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_inv : s⁻¹.snd = s.fst⁻¹ :=
  rfl

@[to_additive (attr := simp)]
/-
**NonemptyInterval.coe_inv_interval** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`
。
形式化陈述：coe_inv_interval : (↑(s⁻¹) : Interval α) = (↑s)⁻¹
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inv_interval : (↑(s⁻¹) : Interval α) = (↑s)⁻¹ :=
  rfl

@[to_additive]
/-
**NonemptyInterval.inv_mem_inv** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：inv_mem_inv (ha : a in s) : a⁻¹ in s⁻¹
参数：ha : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_le_inv'`：inv_le_inv' : a <= b -> b⁻¹ <= a⁻¹
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem inv_mem_inv (ha : a ∈ s) : a⁻¹ ∈ s⁻¹ :=
  ⟨inv_le_inv' ha.2, inv_le_inv' ha.1⟩

@[to_additive (attr := simp)]
/-
**NonemptyInterval.inv_pure** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：inv_pure : (pure a)⁻¹ = pure a⁻¹
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_pure : (pure a)⁻¹ = pure a⁻¹ :=
  rfl

end NonemptyInterval

@[to_additive (attr := simp)]
/-
**Interval.inv_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Interval.inv_bot : (⊥ : Interval α)⁻¹ = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Interval.inv_bot : (⊥ : Interval α)⁻¹ = ⊥ :=
  rfl

end Inv

namespace NonemptyInterval

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {s t : NonemptyInterval α}

@[to_additive]
/-
**NonemptyInterval.mul_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：∀ {α : Type u_2} [inst : CommGroup α] [inst_1 : PartialOrder α] [inst_2 : 
IsOrderedMonoid α] {s t : NonemptyInterval α},   s * t = 1 ↔ ∃ a b, s = Nonempty
Interval.pure a ∧ t = NonemptyInterval.pure b ∧ a * b = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_le_mul_iff_of_ge`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : PartialO
rder α] [MulLeftStrictMono α] [MulRightStrictMono α]   {a₁ a₂ b₁ b₂ : α}, a₁ ≤ a
₂ → b₁ ≤ b…
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
· 使用定理 `IsOrderedMonoid.toIsOrderedCancelMonoid`：∀ {α : Type u} [inst : CommGrou
p α] [inst_1 : Preorder α] [IsOrderedMonoid α], IsOrderedCancelMonoid α
· 使用定理 `NonemptyInterval.fst_le_snd`：∀ {α : Type u_6} [inst : LE α] (self : None
mptyInterval α), self.toProd.1 ≤ self.toProd.2
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
· 使用定理 `NonemptyInterval.ext_iff`：∀ {α : Type u_6} {inst : LE α} {x y : Nonempty
Interval α}, x = y ↔ x.toProd = y.toProd
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `NonemptyInterval.ext`：∀ {α : Type u_6} {inst : LE α} {x y : NonemptyInte
rval α}, x.toProd = y.toProd → x = y
· 使用定理 `NonemptyInterval.pure_mul_pure`：pure_mul_pure : pure a * pure b = pure (
a * b)
· 使用定理 `NonemptyInterval.pure_one`：pure_one : pure (1 : α) = 1
-/
protected theorem mul_eq_one_iff : s * t = 1 ↔ ∃ a b, s = pure a ∧ t = pure b ∧ a * b = 1 := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [NonemptyInterval.ext_iff, Prod.ext_iff] at h
    have := (mul_le_mul_iff_of_ge s.fst_le_snd t.fst_le_snd).1 (h.2.trans h.1.symm).le
    refine ⟨s.fst, t.fst, ?_, ?_, h.1⟩ <;> apply NonemptyInterval.ext <;> dsimp [pure]
    · nth_rw 2 [this.1]
    · nth_rw 2 [this.2]
  · rintro ⟨b, c, rfl, rfl, h⟩
    rw [pure_mul_pure, h, pure_one]
/-
**NonemptyInterval.subtractionCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInte
rval`。
形式化陈述：subtractionCommMonoid {α : Type u} [AddCommGroup α] [PartialOrder α] [IsOr
deredAddMonoid α] : SubtractionCommMonoid (NonemptyInterval α) where sub_eq_add_
neg
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
    rw [neg_pure, neg_eq_of_add_eq_zero_right hab]
  -- TODO: use a better defeq
  zsmul := zsmulRec

@[to_additive existing NonemptyInterval.subtractionCommMonoid]
/-
**NonemptyInterval.divisionCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyInterva
l`。
形式化陈述：divisionCommMonoid : DivisionCommMonoid (NonemptyInterval α) where div_eq_
mul_inv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
    rw [inv_pure, inv_eq_of_mul_eq_one_right hab]

end NonemptyInterval

namespace Interval

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {s t : Interval α}

@[to_additive]
/-
**Interval.mul_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：∀ {α : Type u_2} [inst : CommGroup α] [inst_1 : PartialOrder α] [inst_2 : 
IsOrderedMonoid α] {s t : Interval α},   s * t = 1 ↔ ∃ a b, s = Interval.pure a 
∧ t = Interval.pure b ∧ a * b = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Interval.bot_mul`：bot_mul : ⊥ * t = ⊥
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Interval.mul_bot`：mul_bot : s * ⊥ = ⊥
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `NonemptyInterval.mul_eq_one_iff`：∀ {α : Type u_2} [inst : CommGroup α] [
inst_1 : PartialOrder α] [inst_2 : IsOrderedMonoid α] {s t : NonemptyInterval α}
,   s * t = 1 ↔ ∃ a b…
-/
protected theorem mul_eq_one_iff : s * t = 1 ↔ ∃ a b, s = pure a ∧ t = pure b ∧ a * b = 1 := by
  cases s
  · simp
  cases t
  · simp
  · simp_rw [← NonemptyInterval.coe_mul_interval, ← NonemptyInterval.coe_one_interval,
      Interval.coe_inj, NonemptyInterval.coe_eq_pure]
    exact NonemptyInterval.mul_eq_one_iff
/-
**Interval.subtractionCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Interval`。
形式化陈述：subtractionCommMonoid {α : Type u} [AddCommGroup α] [PartialOrder α] [IsOr
deredAddMonoid α] : SubtractionCommMonoid (Interval α) where sub_eq_add_neg
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**Interval.divisionCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Interval`。
形式化陈述：divisionCommMonoid : DivisionCommMonoid (Interval α) where div_eq_mul_inv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-- The length of an interval is its first component minus its second component. This measures the
accuracy of the approximation by an interval. -/
/-
**NonemptyInterval.length** 是 Mathlib 中的一个定义，位于命名空间 `NonemptyInterval`。
形式化陈述：length : α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The length of an interval is its first component minus its second component. Thi
s measures the
accuracy of the approximation by an interval.
-/
def length : α :=
  s.snd - s.fst

@[simp]
/-
**NonemptyInterval.length_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：length_nonneg : 0 <= s.length
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_nonneg_of_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, b ≤ a → 0 ≤ a - b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `NonemptyInterval.fst_le_snd`：∀ {α : Type u_6} [inst : LE α] (self : None
mptyInterval α), self.toProd.1 ≤ self.toProd.2
-/
theorem length_nonneg : 0 ≤ s.length :=
  sub_nonneg_of_le s.fst_le_snd

omit [IsOrderedAddMonoid α] in
@[simp]
/-
**NonemptyInterval.length_pure** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：length_pure : (pure a).length = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem length_pure : (pure a).length = 0 :=
  sub_self _

omit [IsOrderedAddMonoid α] in
@[simp]
/-
**NonemptyInterval.length_zero** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：length_zero : (0 : NonemptyInterval α).length = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonemptyInterval.length_pure`：length_pure : (pure a).length = 0
-/
theorem length_zero : (0 : NonemptyInterval α).length = 0 :=
  length_pure _

@[simp]
/-
**NonemptyInterval.length_neg** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：length_neg : (-s).length = s.length
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `neg_sub_neg`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α)
, -a - -b = b - a
-/
theorem length_neg : (-s).length = s.length :=
  neg_sub_neg _ _

@[simp]
/-
**NonemptyInterval.length_add** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：length_add : (s + t).length = s.length + t.length
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_sub_add_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a + b - (c + d) = a - c + (b - d)
-/
theorem length_add : (s + t).length = s.length + t.length :=
  add_sub_add_comm _ _ _ _

@[simp]
/-
**NonemptyInterval.length_sub** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：length_sub : (s - t).length = s.length + t.length
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `NonemptyInterval.length_add`：length_add : (s + t).length = s.length + t.
length
· 使用定理 `NonemptyInterval.length_neg`：length_neg : (-s).length = s.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem length_sub : (s - t).length = s.length + t.length := by simp [sub_eq_add_neg]

@[simp]
/-
**NonemptyInterval.length_sum** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyInterval`。
形式化陈述：length_sum (f : ι -> NonemptyInterval α) (s : Finset ι) : (∑ i in s, f i).
length = ∑ i in s, (f i).length
参数：f : ι -> NonemptyInterval α；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `NonemptyInterval.length_zero`：length_zero : (0 : NonemptyInterval α).len
gth = 0
· 使用定理 `NonemptyInterval.length_add`：length_add : (s + t).length = s.length + t.
length
-/
theorem length_sum (f : ι → NonemptyInterval α) (s : Finset ι) :
    (∑ i ∈ s, f i).length = ∑ i ∈ s, (f i).length :=
  map_sum (⟨⟨length, length_zero⟩, length_add⟩ : NonemptyInterval α →+ α) _ _

end NonemptyInterval

namespace Interval

variable (s t : Interval α) (a : α)

/-- The length of an interval is its first component minus its second component. This measures the
accuracy of the approximation by an interval. -/
/-
**Interval.length** 是 Mathlib 中的一个定义，位于命名空间 `Interval`。
形式化陈述：{α : Type u_2} → [AddCommGroup α] → [inst : PartialOrder α] → Interval α →
 α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The length of an interval is its first component minus its second component. Thi
s measures the
accuracy of the approximation by an interval.
-/
def length : Interval α → α
  | ⊥ => 0
  | (s : NonemptyInterval α) => s.length

@[simp]
/-
**Interval.length_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：∀ {α : Type u_2} [inst : AddCommGroup α] [inst_1 : PartialOrder α] [IsOrde
redAddMonoid α] (s : Interval α), 0 ≤ s.length
参数：s : Interval α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `NonemptyInterval.length_nonneg`：length_nonneg : 0 <= s.length
-/
theorem length_nonneg : ∀ s : Interval α, 0 ≤ s.length
  | ⊥ => le_rfl
  | (s : NonemptyInterval α) => s.length_nonneg

omit [IsOrderedAddMonoid α] in
@[simp]
/-
**Interval.length_pure** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：length_pure : (pure a).length = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonemptyInterval.length_pure`：length_pure : (pure a).length = 0
-/
theorem length_pure : (pure a).length = 0 :=
  NonemptyInterval.length_pure _

omit [IsOrderedAddMonoid α] in
@[simp]
/-
**Interval.length_zero** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：length_zero : (0 : Interval α).length = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Interval.length_pure`：length_pure : (pure a).length = 0
-/
theorem length_zero : (0 : Interval α).length = 0 :=
  length_pure _

@[simp]
/-
**Interval.length_neg** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：∀ {α : Type u_2} [inst : AddCommGroup α] [inst_1 : PartialOrder α] [inst_2
 : IsOrderedAddMonoid α] (s : Interval α),   (-s).length = s.length
参数：s : Interval α；-s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonemptyInterval.length_neg`：length_neg : (-s).length = s.length
-/
theorem length_neg : ∀ s : Interval α, (-s).length = s.length
  | ⊥ => rfl
  | (s : NonemptyInterval α) => s.length_neg

omit [IsOrderedAddMonoid α] in
@[simp]
/-
**Interval.length_bot** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：length_bot : (⊥ : Interval α).length = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem length_bot : (⊥ : Interval α).length = 0 := rfl
/-
**Interval.length_add_le** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：∀ {α : Type u_2} [inst : AddCommGroup α] [inst_1 : PartialOrder α] [inst_2
 : IsOrderedAddMonoid α] (s t : Interval α),   (s + t).length ≤ s.length + t.len
gth
参数：s t : Interval α；s + t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Interval.bot_add`：∀ {α : Type u_2} [inst : Preorder α] [inst_1 : Add α] 
[inst_2 : AddLeftMono α] [inst_3 : AddRightMono α]   (t : Interval α), ⊥ + t = ⊥
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Interval.add_bot`：∀ {α : Type u_2} [inst : Preorder α] [inst_1 : Add α] 
[inst_2 : AddLeftMono α] [inst_3 : AddRightMono α]   (s : Interval α), s + ⊥ = ⊥
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `NonemptyInterval.length_add`：length_add : (s + t).length = s.length + t.
length
-/
theorem length_add_le : ∀ s t : Interval α, (s + t).length ≤ s.length + t.length
  | ⊥, _ => by simp
  | _, ⊥ => by simp
  | (s : NonemptyInterval α), (t : NonemptyInterval α) => (s.length_add t).le
/-
**Interval.length_sub_le** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：length_sub_le : (s - t).length <= s.length + t.length
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Interval.length_neg`：∀ {α : Type u_2} [inst : AddCommGroup α] [inst_1 : 
PartialOrder α] [inst_2 : IsOrderedAddMonoid α] (s : Interval α),   (-s).length 
= s.lengt…
· 使用定理 `Interval.length_add_le`：∀ {α : Type u_2} [inst : AddCommGroup α] [inst_1
 : PartialOrder α] [inst_2 : IsOrderedAddMonoid α] (s t : Interval α),   (s + t)
.length ≤ s.…
-/
theorem length_sub_le : (s - t).length ≤ s.length + t.length := by
  simpa [sub_eq_add_neg] using length_add_le s (-t)
/-
**Interval.length_sum_le** 是 Mathlib 中的一个定理，位于命名空间 `Interval`。
形式化陈述：length_sum_le (f : ι -> Interval α) (s : Finset ι) : (∑ i in s, f i).lengt
h <= ∑ i in s, (f i).length
参数：f : ι -> Interval α；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.le_sum_of_subadditive`：∀ {ι : Type u_1} {M : Type u_4} {N : Type 
u_5} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N] [inst_2 : Preorder N]  
 [IsOrderedAddMono…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Interval.length_zero`：length_zero : (0 : Interval α).length = 0
· 使用定理 `Interval.length_add_le`：∀ {α : Type u_2} [inst : AddCommGroup α] [inst_1
 : PartialOrder α] [inst_2 : IsOrderedAddMonoid α] (s t : Interval α),   (s + t)
.length ≤ s.…
-/
theorem length_sum_le (f : ι → Interval α) (s : Finset ι) :
    (∑ i ∈ s, f i).length ≤ ∑ i ∈ s, (f i).length :=
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

