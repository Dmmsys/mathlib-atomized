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

/-
**Nat.instMulLeftMono** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Nat.instMulLeftMono : MulLeftMono Nat where elim
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mul_le_mul_left`：∀ {n m : ℕ} (k : ℕ), n ≤ m → k * n ≤ k * m
-/
instance Nat.instMulLeftMono : MulLeftMono ℕ where
  elim := fun _ _ _ h => mul_le_mul_left _ h

end Nat

section Int

/-
**Int.instAddLeftMono** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Int.instAddLeftMono : AddLeftMono Int where elim
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.add_le_add_left`：∀ {a b : ℤ}, a ≤ b → ∀ (c : ℤ), c + a ≤ c + b
-/
instance Int.instAddLeftMono : AddLeftMono ℤ where
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
/-
**mul_le_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= c) (a : α) : a * b <
= a * c
参数：bc : b <= c；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N} {r 
: N → N → Prop} [self : CovariantClass M N μ r], Covariant M N μ r
-/
theorem mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b ≤ c) (a : α) : a * b ≤ a * c :=
  CovariantClass.elim _ bc

@[to_additive (attr := to_dual self) le_of_add_le_add_left]
/-
**le_of_mul_le_mul_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_mul_le_mul_left' [MulLeftReflectLE α] {a b c : α} (bc : a * b <= a *
 c) : b <= c
参数：bc : a * b <= a * c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulLeftReflectLE.le_of_mul_le_mul_left'`：∀ {M : Type u_1} {inst : Mul M}
 {inst_1 : LE M} [self : MulLeftReflectLE M] {a b₁ b₂ : M}, a * b₁ ≤ a * b₂ → b₁
 ≤ b₂
-/
theorem le_of_mul_le_mul_left' [MulLeftReflectLE α] {a b c : α} (bc : a * b ≤ a * c) : b ≤ c :=
  MulLeftReflectLE.le_of_mul_le_mul_left' bc

@[to_additive (attr := gcongr high - 1, to_dual self)]
/-
**mul_le_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b <= c) (a : α) : b *
 a <= c * a
参数：bc : b <= c；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N} {r 
: N → N → Prop} [self : CovariantClass M N μ r], Covariant M N μ r
-/
theorem mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b ≤ c) (a : α) : b * a ≤ c * a :=
  i.elim a bc

@[to_additive (attr := to_dual self) le_of_add_le_add_right]
/-
**le_of_mul_le_mul_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_mul_le_mul_right' [MulRightReflectLE α] {a b c : α} (bc : b * a <= c
 * a) : b <= c
参数：bc : b * a <= c * a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulRightReflectLE.le_of_mul_le_mul_right'`：∀ {M : Type u_1} {inst : Mul 
M} {inst_1 : LE M} [self : MulRightReflectLE M] {b a₁ a₂ : M}, a₁ * b ≤ a₂ * b →
 a₁ ≤ a₂
-/
theorem le_of_mul_le_mul_right' [MulRightReflectLE α] {a b c : α} (bc : b * a ≤ c * a) :
    b ≤ c :=
  MulRightReflectLE.le_of_mul_le_mul_right' bc

@[to_additive (attr := simp, to_dual self)]
/-
**mul_le_mul_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_mul_iff_left [MulLeftMono α] [MulLeftReflectLE α] (a : α) {b c : α}
 : a * b <= a * c ↔ b <= c
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `rel_iff_cov'`：rel_iff_cov' (hcov : Covariant M N μ r) (hcontra : Contrav
ariant M N μ r) {m : M} {a b : N} : r (μ m a) (μ m b) ↔ r a b
· 使用定理 `CovariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N} {r 
: N → N → Prop} [self : CovariantClass M N μ r], Covariant M N μ r
· 使用定理 `MulLeftReflectLE.le_of_mul_le_mul_left'`：∀ {M : Type u_1} {inst : Mul M}
 {inst_1 : LE M} [self : MulLeftReflectLE M] {a b₁ b₂ : M}, a * b₁ ≤ a * b₂ → b₁
 ≤ b₂
-/
theorem mul_le_mul_iff_left [MulLeftMono α] [MulLeftReflectLE α] (a : α) {b c : α} :
    a * b ≤ a * c ↔ b ≤ c :=
  rel_iff_cov' ‹MulLeftMono α›.elim fun _ ↦ MulLeftReflectLE.le_of_mul_le_mul_left'

@[to_additive (attr := simp, to_dual self)]
/-
**mul_le_mul_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_mul_iff_right [MulRightMono α] [MulRightReflectLE α] (a : α) {b c :
 α} : b * a <= c * a ↔ b <= c
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `rel_iff_cov'`：rel_iff_cov' (hcov : Covariant M N μ r) (hcontra : Contrav
ariant M N μ r) {m : M} {a b : N} : r (μ m a) (μ m b) ↔ r a b
· 使用定理 `CovariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N} {r 
: N → N → Prop} [self : CovariantClass M N μ r], Covariant M N μ r
· 使用定理 `MulRightReflectLE.le_of_mul_le_mul_right'`：∀ {M : Type u_1} {inst : Mul 
M} {inst_1 : LE M} [self : MulRightReflectLE M] {b a₁ a₂ : M}, a₁ * b ≤ a₂ * b →
 a₁ ≤ a₂
-/
theorem mul_le_mul_iff_right [MulRightMono α] [MulRightReflectLE α] (a : α) {b c : α} :
    b * a ≤ c * a ↔ b ≤ c :=
  rel_iff_cov' ‹MulRightMono α›.elim fun _ ↦ MulRightReflectLE.le_of_mul_le_mul_right'

end LE

section LT

variable [LT α]

@[to_additive (attr := simp, to_dual self)]
/-
**mul_lt_mul_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_mul_iff_left [MulLeftStrictMono α] [MulLeftReflectLT α] (a : α) {b 
c : α} : a * b < a * c ↔ b < c
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `rel_iff_cov`：rel_iff_cov [CovariantClass M N μ r] [ContravariantClass M 
N μ r] (m : M) {a b : N} : r (μ m a) (μ m b) ↔ r a b
-/
theorem mul_lt_mul_iff_left [MulLeftStrictMono α]
    [MulLeftReflectLT α] (a : α) {b c : α} :
    a * b < a * c ↔ b < c :=
  rel_iff_cov α α (· * ·) (· < ·) a

@[to_additive (attr := simp, to_dual self)]
/-
**mul_lt_mul_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_mul_iff_right [MulRightStrictMono α] [MulRightReflectLT α] (a : α) 
{b c : α} : b * a < c * a ↔ b < c
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `rel_iff_cov`：rel_iff_cov [CovariantClass M N μ r] [ContravariantClass M 
N μ r] (m : M) {a b : N} : r (μ m a) (μ m b) ↔ r a b
-/
theorem mul_lt_mul_iff_right [MulRightStrictMono α]
    [MulRightReflectLT α] (a : α) {b c : α} :
    b * a < c * a ↔ b < c :=
  rel_iff_cov α α (swap (· * ·)) (· < ·) a

-- Note: in this section, we use `@[gcongr high]` so that these lemmas have a higher priority than
-- lemmas like `mul_lt_mul_of_pos_left`, which have an extra side condition.

@[to_additive (attr := gcongr high, to_dual self)]
/-
**mul_lt_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_mul_right [MulLeftStrictMono α] {b c : α} (bc : b < c) (a : α) : a 
* b < a * c
参数：bc : b < c；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N} {r 
: N → N → Prop} [self : CovariantClass M N μ r], Covariant M N μ r
-/
theorem mul_lt_mul_right [MulLeftStrictMono α] {b c : α} (bc : b < c) (a : α) :
    a * b < a * c :=
  CovariantClass.elim _ bc

@[to_additive (attr := to_dual self) lt_of_add_lt_add_left]
/-
**lt_of_mul_lt_mul_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_of_mul_lt_mul_left' [MulLeftReflectLT α] {a b c : α} (bc : a * b < a * 
c) : b < c
参数：bc : a * b < a * c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContravariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N}
 {r : N → N → Prop} [self : ContravariantClass M N μ r],   Contravariant M N μ r
-/
theorem lt_of_mul_lt_mul_left' [MulLeftReflectLT α] {a b c : α}
    (bc : a * b < a * c) :
    b < c :=
  ContravariantClass.elim _ bc

@[to_additive (attr := gcongr high, to_dual self)]
/-
**mul_lt_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_mul_left [i : MulRightStrictMono α] {b c : α} (bc : b < c) (a : α) 
: b * a < c * a
参数：bc : b < c；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N} {r 
: N → N → Prop} [self : CovariantClass M N μ r], Covariant M N μ r
-/
theorem mul_lt_mul_left [i : MulRightStrictMono α] {b c : α} (bc : b < c)
    (a : α) :
    b * a < c * a :=
  i.elim a bc

@[to_additive (attr := to_dual self) lt_of_add_lt_add_right]
/-
**lt_of_mul_lt_mul_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_of_mul_lt_mul_right' [i : MulRightReflectLT α] {a b c : α} (bc : b * a 
< c * a) : b < c
参数：bc : b * a < c * a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContravariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N}
 {r : N → N → Prop} [self : ContravariantClass M N μ r],   Contravariant M N μ r
-/
theorem lt_of_mul_lt_mul_right' [i : MulRightReflectLT α] {a b c : α}
    (bc : b * a < c * a) :
    b < c :=
  i.elim a bc

end LT

section Preorder

variable [Preorder α]

@[to_additive]
/-
**mul_right_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_right_mono [MulLeftMono α] {a : α} : Monotone (a * ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
-/
lemma mul_right_mono [MulLeftMono α] {a : α} : Monotone (a * ·) :=
  fun _ _ h ↦ mul_le_mul_right h _

@[to_additive]
/-
**mul_left_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_left_mono [MulRightMono α] {a : α} : Monotone (· * a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
-/
lemma mul_left_mono [MulRightMono α] {a : α} : Monotone (· * a) :=
  fun _ _ h ↦ mul_le_mul_left h _

@[to_additive]
/-
**mul_right_strictMono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_right_strictMono [MulLeftStrictMono α] {a : α} : StrictMono (a * ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_right`：mul_lt_mul_right [MulLeftStrictMono α] {b c : α} (bc :
 b < c) (a : α) : a * b < a * c
-/
lemma mul_right_strictMono [MulLeftStrictMono α] {a : α} : StrictMono (a * ·) :=
  fun _ _ h ↦ mul_lt_mul_right h _

@[to_additive]
/-
**mul_left_strictMono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_left_strictMono [MulRightStrictMono α] {a : α} : StrictMono (· * a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_left`：mul_lt_mul_left [i : MulRightStrictMono α] {b c : α} (b
c : b < c) (a : α) : b * a < c * a
-/
lemma mul_left_strictMono [MulRightStrictMono α] {a : α} : StrictMono (· * a) :=
  fun _ _ h ↦ mul_lt_mul_left h _

-- Note: in this section, we use `@[gcongr high]` so that these lemmas have a higher priority than
-- lemmas like `mul_le_mul_of_nonneg`, which have an extra side condition.

@[to_additive (attr := gcongr high, to_dual self)]
/-
**mul_lt_mul_of_lt_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_mul_of_lt_of_lt [MulLeftStrictMono α] [MulRightStrictMono α] {a b c
 d : α} (h₁ : a < b) (h₂ : c < d) : a * c < b * d
参数：h₁ : a < b；h₂ : c < d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_right`：mul_lt_mul_right [MulLeftStrictMono α] {b c : α} (bc :
 b < c) (a : α) : a * b < a * c
· 使用定理 `mul_lt_mul_left`：mul_lt_mul_left [i : MulRightStrictMono α] {b c : α} (b
c : b < c) (a : α) : b * a < c * a
-/
theorem mul_lt_mul_of_lt_of_lt [MulLeftStrictMono α]
    [MulRightStrictMono α]
    {a b c d : α} (h₁ : a < b) (h₂ : c < d) : a * c < b * d :=
  calc
    a * c < a * d := mul_lt_mul_right h₂ a
    _ < b * d := mul_lt_mul_left h₁ d

@[to_dual self] alias add_lt_add := add_lt_add_of_lt_of_lt

@[to_additive (attr := to_dual self)]
/-
**mul_lt_mul_of_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_mul_of_le_of_lt [MulLeftStrictMono α] [MulRightMono α] {a b c d : α
} (h₁ : a <= b) (h₂ : c < d) : a * c < b * d
参数：h₁ : a <= b；h₂ : c < d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
· 使用定理 `mul_lt_mul_right`：mul_lt_mul_right [MulLeftStrictMono α] {b c : α} (bc :
 b < c) (a : α) : a * b < a * c
-/
theorem mul_lt_mul_of_le_of_lt [MulLeftStrictMono α]
    [MulRightMono α] {a b c d : α} (h₁ : a ≤ b) (h₂ : c < d) :
    a * c < b * d :=
  (mul_le_mul_left h₁ _).trans_lt (mul_lt_mul_right h₂ b)

@[to_additive (attr := to_dual self)]
/-
**mul_lt_mul_of_lt_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_mul_of_lt_of_le [MulLeftMono α] [MulRightStrictMono α] {a b c d : α
} (h₁ : a < b) (h₂ : c <= d) : a * c < b * d
参数：h₁ : a < b；h₂ : c <= d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
· 使用定理 `mul_lt_mul_left`：mul_lt_mul_left [i : MulRightStrictMono α] {b c : α} (b
c : b < c) (a : α) : b * a < c * a
-/
theorem mul_lt_mul_of_lt_of_le [MulLeftMono α]
    [MulRightStrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c ≤ d) :
    a * c < b * d :=
  (mul_le_mul_right h₂ _).trans_lt (mul_lt_mul_left h₁ d)

/-- Only assumes left strict covariance. -/
@[to_additive (attr := to_dual self) /-- Only assumes left strict covariance -/]
/-
**Left.mul_lt_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Left.mul_lt_mul [MulLeftStrictMono α] [MulRightMono α] {a b c d : α} (h₁ :
 a < b) (h₂ : c < d) : a * c < b * d
参数：h₁ : a < b；h₂ : c < d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_of_le_of_lt`：mul_lt_mul_of_le_of_lt [MulLeftStrictMono α] [Mu
lRightMono α] {a b c d : α} (h₁ : a <= b) (h₂ : c < d) : a * c < b * d
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
Only assumes left strict covariance.
-/
theorem Left.mul_lt_mul [MulLeftStrictMono α]
    [MulRightMono α] {a b c d : α} (h₁ : a < b) (h₂ : c < d) :
    a * c < b * d :=
  mul_lt_mul_of_le_of_lt h₁.le h₂

/-- Only assumes right strict covariance. -/
@[to_additive (attr := to_dual self) /-- Only assumes right strict covariance -/]
/-
**Right.mul_lt_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.mul_lt_mul [MulLeftMono α] [MulRightStrictMono α] {a b c d : α} (h₁ 
: a < b) (h₂ : c < d) : a * c < b * d
参数：h₁ : a < b；h₂ : c < d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_of_lt_of_le`：mul_lt_mul_of_lt_of_le [MulLeftMono α] [MulRight
StrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c <= d) : a * c < b * d
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
Only assumes right strict covariance.
-/
theorem Right.mul_lt_mul [MulLeftMono α]
    [MulRightStrictMono α] {a b c d : α}
    (h₁ : a < b) (h₂ : c < d) :
    a * c < b * d :=
  mul_lt_mul_of_lt_of_le h₁ h₂.le

@[to_additive (attr := gcongr high, to_dual self) add_le_add]
/-
**mul_le_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} (h₁ : a <= b) (
h₂ : c <= d) : a * c <= b * d
参数：h₁ : a <= b；h₂ : c <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
-/
theorem mul_le_mul' [MulLeftMono α] [MulRightMono α]
    {a b c d : α} (h₁ : a ≤ b) (h₂ : c ≤ d) :
    a * c ≤ b * d := by grw [h₁, h₂]

@[to_additive (attr := to_dual self)]
/-
**mul_le_mul_three** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_mul_three [MulLeftMono α] [MulRightMono α] {a b c d e f : α} (h₁ : 
a <= d) (h₂ : b <= e) (h₃ : c <= f) : a * b * c <= d * e * f
参数：h₁ : a <= d；h₂ : b <= e；h₃ : c <= f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
-/
theorem mul_le_mul_three [MulLeftMono α]
    [MulRightMono α] {a b c d e f : α} (h₁ : a ≤ d) (h₂ : b ≤ e)
    (h₃ : c ≤ f) :
    a * b * c ≤ d * e * f :=
  mul_le_mul' (mul_le_mul' h₁ h₂) h₃

@[to_additive]
/-
**mul_lt_of_mul_lt_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_of_mul_lt_left [MulLeftMono α] {a b c d : α} (h : a * b < c) (hle :
 d <= b) : a * d < c
参数：h : a * b < c；hle : d <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
-/
theorem mul_lt_of_mul_lt_left [MulLeftMono α] {a b c d : α} (h : a * b < c)
    (hle : d ≤ b) :
    a * d < c :=
  (mul_le_mul_right hle a).trans_lt h

@[to_additive]
/-
**mul_le_of_mul_le_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_of_mul_le_left [MulLeftMono α] {a b c d : α} (h : a * b <= c) (hle 
: d <= b) : a * d <= c
参数：h : a * b <= c；hle : d <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `act_rel_of_rel_of_act_rel`：act_rel_of_rel_of_act_rel (ab : r a b) (rl : 
r (μ m b) c) : r (μ m a) c
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
-/
theorem mul_le_of_mul_le_left [MulLeftMono α] {a b c d : α} (h : a * b ≤ c)
    (hle : d ≤ b) :
    a * d ≤ c :=
  @act_rel_of_rel_of_act_rel _ _ _ (· ≤ ·) _ _ a _ _ _ hle h

@[to_additive]
/-
**mul_lt_of_mul_lt_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_of_mul_lt_right [MulRightMono α] {a b c d : α} (h : a * b < c) (hle
 : d <= a) : d * b < c
参数：h : a * b < c；hle : d <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
-/
theorem mul_lt_of_mul_lt_right [MulRightMono α] {a b c d : α}
    (h : a * b < c) (hle : d ≤ a) :
    d * b < c :=
  (mul_le_mul_left hle b).trans_lt h

@[to_additive]
/-
**mul_le_of_mul_le_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_of_mul_le_right [MulRightMono α] {a b c d : α} (h : a * b <= c) (hl
e : d <= a) : d * b <= c
参数：h : a * b <= c；hle : d <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
-/
theorem mul_le_of_mul_le_right [MulRightMono α] {a b c d : α}
    (h : a * b ≤ c) (hle : d ≤ a) :
    d * b ≤ c :=
  (mul_le_mul_left hle b).trans h

@[to_additive]
/-
**lt_mul_of_lt_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_mul_of_lt_mul_left [MulLeftMono α] {a b c d : α} (h : a < b * c) (hle :
 c <= d) : a < b * d
参数：h : a < b * c；hle : c <= d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
-/
theorem lt_mul_of_lt_mul_left [MulLeftMono α] {a b c d : α} (h : a < b * c)
    (hle : c ≤ d) :
    a < b * d :=
  h.trans_le (mul_le_mul_right hle b)

@[to_additive]
/-
**le_mul_of_le_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_mul_of_le_mul_left [MulLeftMono α] {a b c d : α} (h : a <= b * c) (hle 
: c <= d) : a <= b * d
参数：h : a <= b * c；hle : c <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `rel_act_of_rel_of_rel_act`：rel_act_of_rel_of_rel_act (ab : r a b) (rr : 
r c (μ m a)) : r c (μ m b)
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
-/
theorem le_mul_of_le_mul_left [MulLeftMono α] {a b c d : α} (h : a ≤ b * c)
    (hle : c ≤ d) :
    a ≤ b * d :=
  @rel_act_of_rel_of_rel_act _ _ _ (· ≤ ·) _ _ b _ _ _ hle h

@[to_additive]
/-
**lt_mul_of_lt_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_mul_of_lt_mul_right [MulRightMono α] {a b c d : α} (h : a < b * c) (hle
 : b <= d) : a < d * c
参数：h : a < b * c；hle : b <= d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
-/
theorem lt_mul_of_lt_mul_right [MulRightMono α] {a b c d : α}
    (h : a < b * c) (hle : b ≤ d) :
    a < d * c :=
  h.trans_le (mul_le_mul_left hle c)

@[to_additive]
/-
**le_mul_of_le_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_mul_of_le_mul_right [MulRightMono α] {a b c d : α} (h : a <= b * c) (hl
e : b <= d) : a <= d * c
参数：h : a <= b * c；hle : b <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
-/
theorem le_mul_of_le_mul_right [MulRightMono α] {a b c d : α}
    (h : a ≤ b * c) (hle : b ≤ d) :
    a ≤ d * c :=
  h.trans (mul_le_mul_left hle c)

end Preorder

section PartialOrder

variable [PartialOrder α]

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulLeftReflectLE α] : IsLeftCancelMul α where
  mul_left_cancel _ _ _ h := (le_of_mul_le_mul_left' h.le).antisymm (le_of_mul_le_mul_left' h.ge)

@[deprecated (since := "2026-03-14")]
alias add_left_cancel'' := add_left_cancel
@[to_additive existing, deprecated (since := "2026-03-14")]
alias mul_left_cancel'' := mul_left_cancel

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulRightReflectLE α] : IsRightCancelMul α where
  mul_right_cancel _ _ _ h := (le_of_mul_le_mul_right' h.le).antisymm (le_of_mul_le_mul_right' h.ge)

@[deprecated (since := "2026-03-14")]
alias add_right_cancel'' := add_right_cancel
@[to_additive existing, deprecated (since := "2026-03-14")]
alias mul_right_cancel'' := mul_right_cancel
/-
**mul_le_mul_iff_of_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Mul α] [inst_1 : PartialOrder α] [MulLeftStrictMo
no α] [MulRightStrictMono α]   {a₁ a₂ b₁ b₂ : α}, a₁ ≤ a₂ → b₁ ≤ b₂ → (a₂ * b₂ ≤
 a₁ * b₁ ↔ a₁ = a₂ ∧ b₁ = b₂)
参数：a₂ * b₂ ≤ a₁ * b₁ ↔ a₁ = a₂ ∧ b₁ = b₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mulLeftMono_of_mulLeftStrictMono`：mulLeftMono_of_mulLeftStrictMono (M) [
Mul M] [PartialOrder M] [MulLeftStrictMono M] : MulLeftMono M
· 使用定理 `mulRightMono_of_mulRightStrictMono`：mulRightMono_of_mulRightStrictMono (
M) [Mul M] [PartialOrder M] [MulRightStrictMono M] : MulRightMono M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `mul_lt_mul_of_lt_of_le`：mul_lt_mul_of_lt_of_le [MulLeftMono α] [MulRight
StrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c <= d) : a * c < b * d
· 使用定理 `mul_lt_mul_of_le_of_lt`：mul_lt_mul_of_le_of_lt [MulLeftStrictMono α] [Mu
lRightMono α] {a b c d : α} (h₁ : a <= b) (h₂ : c < d) : a * c < b * d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
@[to_additive] lemma mul_le_mul_iff_of_ge [MulLeftStrictMono α]
    [MulRightStrictMono α] {a₁ a₂ b₁ b₂ : α} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    a₂ * b₂ ≤ a₁ * b₁ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  have := mulLeftMono_of_mulLeftStrictMono α
  have := mulRightMono_of_mulRightStrictMono α
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, ha, hb, true_and]
  refine ⟨fun ha ↦ h.not_gt ?_, fun hb ↦ h.not_gt ?_⟩
  exacts [mul_lt_mul_of_lt_of_le ha hb, mul_lt_mul_of_le_of_lt ha hb]
/-
**mul_eq_mul_iff_eq_and_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Mul α] [inst_1 : PartialOrder α] [MulLeftStrictMo
no α] [MulRightStrictMono α] {a b c d : α},   a ≤ c → b ≤ d → (a * b = c * d ↔ a
 = c ∧ b = d)
参数：a * b = c * d ↔ a = c ∧ b = d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mulLeftMono_of_mulLeftStrictMono`：mulLeftMono_of_mulLeftStrictMono (M) [
Mul M] [PartialOrder M] [MulLeftStrictMono M] : MulLeftMono M
· 使用定理 `mulRightMono_of_mulRightStrictMono`：mulRightMono_of_mulRightStrictMono (
M) [Mul M] [PartialOrder M] [MulRightStrictMono M] : MulRightMono M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `mul_le_mul_iff_of_ge`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : PartialO
rder α] [MulLeftStrictMono α] [MulRightStrictMono α]   {a₁ a₂ b₁ b₂ : α}, a₁ ≤ a
₂ → b₁ ≤ b…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_additive] theorem mul_eq_mul_iff_eq_and_eq [MulLeftStrictMono α]
    [MulRightStrictMono α] {a b c d : α} (hac : a ≤ c) (hbd : b ≤ d) :
    a * b = c * d ↔ a = c ∧ b = d := by
  have := mulLeftMono_of_mulLeftStrictMono α
  have := mulRightMono_of_mulRightStrictMono α
  rw [le_antisymm_iff, eq_true (mul_le_mul' hac hbd), true_and, mul_le_mul_iff_of_ge hac hbd]

@[to_additive]
/-
**mul_left_inj_of_comparable** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_left_inj_of_comparable [MulRightStrictMono α] {a b c : α} (h : b <= c 
∨ c <= b) : c * a = b * a ↔ c = b
参数：h : b <= c ∨ c <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `mul_lt_mul_left`：mul_lt_mul_left [i : MulRightStrictMono α] {b c : α} (b
c : b < c) (a : α) : b * a < c * a
· 使用定理 `LE.le.lt_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
-/
lemma mul_left_inj_of_comparable [MulRightStrictMono α] {a b c : α} (h : b ≤ c ∨ c ≤ b) :
    c * a = b * a ↔ c = b := by
  refine ⟨fun h' => ?_, (· ▸ rfl)⟩
  contrapose h'
  obtain h | h := h
  · exact mul_lt_mul_left (h.lt_of_ne' h') a |>.ne'
  · exact mul_lt_mul_left (h.lt_of_ne h') a |>.ne

@[to_additive]
/-
**mul_right_inj_of_comparable** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_right_inj_of_comparable [MulLeftStrictMono α] {a b c : α} (h : b <= c 
∨ c <= b) : a * c = a * b ↔ c = b
参数：h : b <= c ∨ c <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `mul_lt_mul_right`：mul_lt_mul_right [MulLeftStrictMono α] {b c : α} (bc :
 b < c) (a : α) : a * b < a * c
· 使用定理 `LE.le.lt_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
-/
lemma mul_right_inj_of_comparable [MulLeftStrictMono α] {a b c : α} (h : b ≤ c ∨ c ≤ b) :
    a * c = a * b ↔ c = b := by
  refine ⟨fun h' => ?_, (· ▸ rfl)⟩
  contrapose h'
  obtain h | h := h
  · exact mul_lt_mul_right (h.lt_of_ne' h') a |>.ne'
  · exact mul_lt_mul_right (h.lt_of_ne h') a |>.ne

end PartialOrder

section LinearOrder
variable [LinearOrder α] {a b c d : α}

@[to_additive]
/-
**trichotomy_of_mul_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trichotomy_of_mul_eq_mul [MulLeftStrictMono α] [MulRightStrictMono α] (h :
 a * b = c * d) : (a = c ∧ b = d) ∨ a < c ∨ b < d
参数：h : a * b = c * d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `mul_right_inj_of_comparable`：mul_right_inj_of_comparable [MulLeftStrictM
ono α] {a b c : α} (h : b <= c ∨ c <= b) : a * c = a * b ↔ c = b
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `mul_lt_mul_left`：mul_lt_mul_left [i : MulRightStrictMono α] {b c : α} (b
c : b < c) (a : α) : b * a < c * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_lt_mul_of_lt_of_lt`：mul_lt_mul_of_lt_of_lt [MulLeftStrictMono α] [Mu
lRightStrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c < d) : a * c < b * d
-/
theorem trichotomy_of_mul_eq_mul
    [MulLeftStrictMono α] [MulRightStrictMono α]
    (h : a * b = c * d) : (a = c ∧ b = d) ∨ a < c ∨ b < d := by
  obtain hac | rfl | hca := lt_trichotomy a c
  · grind
  · left; simpa using mul_right_inj_of_comparable (le_total d b) |>.1 h
  · obtain hbd | rfl | hdb := lt_trichotomy b d
    · grind
    · exact False.elim <| ne_of_lt (mul_lt_mul_left hca b) h.symm
    · exact False.elim <| ne_of_lt (mul_lt_mul_of_lt_of_lt hca hdb) h.symm

@[to_additive]
/-
**mul_max** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_max [MulLeftMono α] (a b c : α) : a * max b c = max (a * b) (a * c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用引理 `mul_right_mono`：mul_right_mono [MulLeftMono α] {a : α} : Monotone (a * ·
)
-/
lemma mul_max [MulLeftMono α] (a b c : α) :
    a * max b c = max (a * b) (a * c) := mul_right_mono.map_max

@[to_additive]
/-
**max_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：max_mul [MulRightMono α] (a b c : α) : max a b * c = max (a * c) (b * c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用引理 `mul_left_mono`：mul_left_mono [MulRightMono α] {a : α} : Monotone (· * a)
-/
lemma max_mul [MulRightMono α] (a b c : α) :
    max a b * c = max (a * c) (b * c) := mul_left_mono.map_max

@[to_additive]
/-
**mul_min** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_min [MulLeftMono α] (a b c : α) : a * min b c = min (a * b) (a * c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用引理 `mul_right_mono`：mul_right_mono [MulLeftMono α] {a : α} : Monotone (a * ·
)
-/
lemma mul_min [MulLeftMono α] (a b c : α) :
    a * min b c = min (a * b) (a * c) := mul_right_mono.map_min

@[to_additive]
/-
**min_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：min_mul [MulRightMono α] (a b c : α) : min a b * c = min (a * c) (b * c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用引理 `mul_left_mono`：mul_left_mono [MulRightMono α] {a : α} : Monotone (· * a)
-/
lemma min_mul [MulRightMono α] (a b c : α) :
    min a b * c = min (a * c) (b * c) := mul_left_mono.map_min
/-
**min_lt_max_of_mul_lt_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Mul α] [inst_1 : LinearOrder α] {a b c d : α} [Mu
lLeftMono α] [MulRightMono α],   a * b < c * d → min a b < max c d
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
@[to_additive] lemma min_lt_max_of_mul_lt_mul
    [MulLeftMono α] [MulRightMono α]
    (h : a * b < c * d) : min a b < max c d := by
  simp_rw [min_lt_iff, lt_max_iff]; contrapose! h; exact mul_le_mul' h.1.1 h.2.2
/-
**Left.min_le_max_of_mul_le_mul** 是 Mathlib 中的一个定理，位于命名空间 `Left`。
形式化陈述：∀ {α : Type u_1} [inst : Mul α] [inst_1 : LinearOrder α] {a b c d : α} [Mu
lLeftStrictMono α] [MulRightMono α],   a * b ≤ c * d → min a b ≤ max c d
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_lt_mul_of_le_of_lt`：mul_lt_mul_of_le_of_lt [MulLeftStrictMono α] [Mu
lRightMono α] {a b c d : α} (h₁ : a <= b) (h₂ : c < d) : a * c < b * d
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
@[to_additive] lemma Left.min_le_max_of_mul_le_mul
    [MulLeftStrictMono α] [MulRightMono α]
    (h : a * b ≤ c * d) : min a b ≤ max c d := by
  simp_rw [min_le_iff, le_max_iff]; contrapose! h; exact mul_lt_mul_of_le_of_lt h.1.1.le h.2.2
/-
**Right.min_le_max_of_mul_le_mul** 是 Mathlib 中的一个定理，位于命名空间 `Right`。
形式化陈述：∀ {α : Type u_1} [inst : Mul α] [inst_1 : LinearOrder α] {a b c d : α} [Mu
lLeftMono α] [MulRightStrictMono α],   a * b ≤ c * d → min a b ≤ max c d
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_lt_mul_of_lt_of_le`：mul_lt_mul_of_lt_of_le [MulLeftMono α] [MulRight
StrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c <= d) : a * c < b * d
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
@[to_additive] lemma Right.min_le_max_of_mul_le_mul
    [MulLeftMono α] [MulRightStrictMono α]
    (h : a * b ≤ c * d) : min a b ≤ max c d := by
  simp_rw [min_le_iff, le_max_iff]; contrapose! h; exact mul_lt_mul_of_lt_of_le h.1.1 h.2.2.le
/-
**min_le_max_of_mul_le_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Mul α] [inst_1 : LinearOrder α] {a b c d : α} [Mu
lLeftStrictMono α] [MulRightStrictMono α],   a * b ≤ c * d → min a b ≤ max c d
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Left.min_le_max_of_mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 :
 LinearOrder α] {a b c d : α} [MulLeftStrictMono α] [MulRightMono α],   a * b ≤ 
c * d → min a b ≤ m…
· 使用定理 `mulRightMono_of_mulRightStrictMono`：mulRightMono_of_mulRightStrictMono (
M) [Mul M] [PartialOrder M] [MulRightStrictMono M] : MulRightMono M
-/
@[to_additive] lemma min_le_max_of_mul_le_mul
    [MulLeftStrictMono α] [MulRightStrictMono α]
    (h : a * b ≤ c * d) : min a b ≤ max c d :=
  haveI := mulRightMono_of_mulRightStrictMono α
  Left.min_le_max_of_mul_le_mul h

/-- Not an instance, to avoid loops with `IsLeftCancelMul.mulLeftStrictMono_of_mulLeftMono`. -/
@[to_additive]
/-
**MulLeftStrictMono.toIsLeftCancelMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulLeftStrictMono.toIsLeftCancelMul [MulLeftStrictMono α] : IsLeftCancelMu
l α where mul_left_cancel _ _ _ h
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用引理 `mul_right_strictMono`：mul_right_strictMono [MulLeftStrictMono α] {a : α}
 : StrictMono (a * ·)

--- 原说明 ---
Not an instance, to avoid loops with `IsLeftCancelMul.mulLeftStrictMono_of_mulLe
ftMono`.
-/
theorem MulLeftStrictMono.toIsLeftCancelMul [MulLeftStrictMono α] : IsLeftCancelMul α where
  mul_left_cancel _ _ _ h := mul_right_strictMono.injective h

/-- Not an instance, to avoid loops with `IsRightCancelMul.mulRightStrictMono_of_mulRightMono`. -/
@[to_additive]
/-
**MulRightStrictMono.toIsRightCancelMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulRightStrictMono.toIsRightCancelMul [MulRightStrictMono α] : IsRightCanc
elMul α where mul_right_cancel _ _ _ h
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用引理 `mul_left_strictMono`：mul_left_strictMono [MulRightStrictMono α] {a : α} 
: StrictMono (· * a)

--- 原说明 ---
Not an instance, to avoid loops with `IsRightCancelMul.mulRightStrictMono_of_mul
RightMono`.
-/
theorem MulRightStrictMono.toIsRightCancelMul [MulRightStrictMono α] : IsRightCancelMul α where
  mul_right_cancel _ _ _ h := mul_left_strictMono.injective h

end LinearOrder

section LinearOrder
variable [LinearOrder α] [MulLeftMono α] [MulRightMono α] {a b c d : α}

@[to_additive max_add_add_le_max_add_max]
/-
**max_mul_mul_le_max_mul_max'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：max_mul_mul_le_max_mul_max' : max (a * b) (c * d) <= max a c * max b d
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem max_mul_mul_le_max_mul_max' : max (a * b) (c * d) ≤ max a c * max b d :=
  max_le (mul_le_mul' (le_max_left _ _) <| le_max_left _ _) <|
    mul_le_mul' (le_max_right _ _) <| le_max_right _ _

@[to_additive min_add_min_le_min_add_add]
/-
**min_mul_min_le_min_mul_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_mul_min_le_min_mul_mul' : min a c * min b d <= min (a * b) (c * d)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_min`：le_min (h₁ : c <= a) (h₂ : c <= b) : c <= min a b
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
-/
theorem min_mul_min_le_min_mul_mul' : min a c * min b d ≤ min (a * b) (c * d) :=
  le_min (mul_le_mul' (min_le_left _ _) <| min_le_left _ _) <|
    mul_le_mul' (min_le_right _ _) <| min_le_right _ _

end LinearOrder
end Mul

-- using one
section MulOneClass

variable [MulOneClass α]

section LE

variable [LE α]

@[to_additive le_add_of_nonneg_right]
/-
**le_mul_of_one_le_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_mul_of_one_le_right' [MulLeftMono α] {a b : α} (h : 1 <= b) : a <= a * 
b
参数：h : 1 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
-/
theorem le_mul_of_one_le_right' [MulLeftMono α] {a b : α} (h : 1 ≤ b) :
    a ≤ a * b :=
  calc
    a = a * 1 := (mul_one a).symm
    _ ≤ a * b := mul_le_mul_right h a

@[to_additive add_le_of_nonpos_right]
/-
**mul_le_of_le_one_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_of_le_one_right' [MulLeftMono α] {a b : α} (h : b <= 1) : a * b <= 
a
参数：h : b <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mul_le_of_le_one_right' [MulLeftMono α] {a b : α} (h : b ≤ 1) :
    a * b ≤ a :=
  calc
    a * b ≤ a * 1 := mul_le_mul_right h a
    _ = a := mul_one a

@[to_additive le_add_of_nonneg_left]
/-
**le_mul_of_one_le_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_mul_of_one_le_left' [MulRightMono α] {a b : α} (h : 1 <= b) : a <= b * 
a
参数：h : 1 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
-/
theorem le_mul_of_one_le_left' [MulRightMono α] {a b : α} (h : 1 ≤ b) :
    a ≤ b * a :=
  calc
    a = 1 * a := (one_mul a).symm
    _ ≤ b * a := mul_le_mul_left h a

@[to_additive add_le_of_nonpos_left]
/-
**mul_le_of_le_one_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_of_le_one_left' [MulRightMono α] {a b : α} (h : b <= 1) : b * a <= 
a
参数：h : b <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem mul_le_of_le_one_left' [MulRightMono α] {a b : α} (h : b ≤ 1) :
    b * a ≤ a :=
  calc
    b * a ≤ 1 * a := mul_le_mul_left h a
    _ = a := one_mul a

@[to_additive]
/-
**one_le_of_le_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_le_of_le_mul_right [MulLeftReflectLE α] {a b : α} (h : a <= a * b) : 1
 <= b
参数：h : a <= a * b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_mul_le_mul_left'`：le_of_mul_le_mul_left' [MulLeftReflectLE α] {a b
 c : α} (bc : a * b <= a * c) : b <= c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem one_le_of_le_mul_right [MulLeftReflectLE α] {a b : α} (h : a ≤ a * b) :
    1 ≤ b :=
  le_of_mul_le_mul_left' (a := a) <| by simpa only [mul_one]

@[to_additive]
/-
**le_one_of_mul_le_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_one_of_mul_le_right [MulLeftReflectLE α] {a b : α} (h : a * b <= a) : b
 <= 1
参数：h : a * b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_mul_le_mul_left'`：le_of_mul_le_mul_left' [MulLeftReflectLE α] {a b
 c : α} (bc : a * b <= a * c) : b <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem le_one_of_mul_le_right [MulLeftReflectLE α] {a b : α} (h : a * b ≤ a) :
    b ≤ 1 :=
  le_of_mul_le_mul_left' (a := a) <| by simpa only [mul_one]

@[to_additive]
/-
**one_le_of_le_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_le_of_le_mul_left [MulRightReflectLE α] {a b : α} (h : b <= a * b) : 1
 <= a
参数：h : b <= a * b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_mul_le_mul_right'`：le_of_mul_le_mul_right' [MulRightReflectLE α] {
a b c : α} (bc : b * a <= c * a) : b <= c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem one_le_of_le_mul_left [MulRightReflectLE α] {a b : α}
    (h : b ≤ a * b) :
    1 ≤ a :=
  le_of_mul_le_mul_right' (a := b) <| by simpa only [one_mul]

@[to_additive]
/-
**le_one_of_mul_le_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_one_of_mul_le_left [MulRightReflectLE α] {a b : α} (h : a * b <= b) : a
 <= 1
参数：h : a * b <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_mul_le_mul_right'`：le_of_mul_le_mul_right' [MulRightReflectLE α] {
a b c : α} (bc : b * a <= c * a) : b <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem le_one_of_mul_le_left [MulRightReflectLE α] {a b : α}
    (h : a * b ≤ b) :
    a ≤ 1 :=
  le_of_mul_le_mul_right' (a := b) <| by simpa only [one_mul]

@[to_additive (attr := simp) le_add_iff_nonneg_right]
/-
**le_mul_iff_one_le_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_mul_iff_one_le_right' [MulLeftMono α] [MulLeftReflectLE α] (a : α) {b :
 α} : a <= a * b ↔ 1 <= b
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `mul_le_mul_iff_left`：mul_le_mul_iff_left [MulLeftMono α] [MulLeftReflect
LE α] (a : α) {b c : α} : a * b <= a * c ↔ b <= c
-/
theorem le_mul_iff_one_le_right' [MulLeftMono α]
    [MulLeftReflectLE α] (a : α) {b : α} :
    a ≤ a * b ↔ 1 ≤ b :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a)

@[to_additive (attr := simp) le_add_iff_nonneg_left]
/-
**le_mul_iff_one_le_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_mul_iff_one_le_left' [MulRightMono α] [MulRightReflectLE α] (a : α) {b 
: α} : a <= b * a ↔ 1 <= b
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `mul_le_mul_iff_right`：mul_le_mul_iff_right [MulRightMono α] [MulRightRef
lectLE α] (a : α) {b c : α} : b * a <= c * a ↔ b <= c
-/
theorem le_mul_iff_one_le_left' [MulRightMono α]
    [MulRightReflectLE α] (a : α) {b : α} :
    a ≤ b * a ↔ 1 ≤ b :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_iff_right a)

@[to_additive (attr := simp) add_le_iff_nonpos_right]
/-
**mul_le_iff_le_one_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_iff_le_one_right' [MulLeftMono α] [MulLeftReflectLE α] (a : α) {b :
 α} : a * b <= a ↔ b <= 1
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `mul_le_mul_iff_left`：mul_le_mul_iff_left [MulLeftMono α] [MulLeftReflect
LE α] (a : α) {b c : α} : a * b <= a * c ↔ b <= c
-/
theorem mul_le_iff_le_one_right' [MulLeftMono α]
    [MulLeftReflectLE α] (a : α) {b : α} :
    a * b ≤ a ↔ b ≤ 1 :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a)

@[to_additive (attr := simp) add_le_iff_nonpos_left]
/-
**mul_le_iff_le_one_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_iff_le_one_left' [MulRightMono α] [MulRightReflectLE α] {a b : α} :
 a * b <= b ↔ a <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `mul_le_mul_iff_right`：mul_le_mul_iff_right [MulRightMono α] [MulRightRef
lectLE α] (a : α) {b c : α} : b * a <= c * a ↔ b <= c
-/
theorem mul_le_iff_le_one_left' [MulRightMono α]
    [MulRightReflectLE α] {a b : α} :
    a * b ≤ b ↔ a ≤ 1 :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_iff_right b)

end LE

section LT

variable [LT α]

@[to_additive lt_add_of_pos_right]
/-
**lt_mul_of_one_lt_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_mul_of_one_lt_right' [MulLeftStrictMono α] (a : α) {b : α} (h : 1 < b) 
: a < a * b
参数：a : α；h : 1 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_lt_mul_right`：mul_lt_mul_right [MulLeftStrictMono α] {b c : α} (bc :
 b < c) (a : α) : a * b < a * c
-/
theorem lt_mul_of_one_lt_right' [MulLeftStrictMono α] (a : α) {b : α} (h : 1 < b) :
    a < a * b :=
  calc
    a = a * 1 := (mul_one a).symm
    _ < a * b := mul_lt_mul_right h a

@[to_additive add_lt_of_neg_right]
/-
**mul_lt_of_lt_one_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_of_lt_one_right' [MulLeftStrictMono α] (a : α) {b : α} (h : b < 1) 
: a * b < a
参数：a : α；h : b < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_right`：mul_lt_mul_right [MulLeftStrictMono α] {b c : α} (bc :
 b < c) (a : α) : a * b < a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mul_lt_of_lt_one_right' [MulLeftStrictMono α] (a : α) {b : α} (h : b < 1) :
    a * b < a :=
  calc
    a * b < a * 1 := mul_lt_mul_right h a
    _ = a := mul_one a

@[to_additive lt_add_of_pos_left]
/-
**lt_mul_of_one_lt_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_mul_of_one_lt_left' [MulRightStrictMono α] (a : α) {b : α} (h : 1 < b) 
: a < b * a
参数：a : α；h : 1 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_lt_mul_left`：mul_lt_mul_left [i : MulRightStrictMono α] {b c : α} (b
c : b < c) (a : α) : b * a < c * a
-/
theorem lt_mul_of_one_lt_left' [MulRightStrictMono α] (a : α) {b : α}
    (h : 1 < b) :
    a < b * a :=
  calc
    a = 1 * a := (one_mul a).symm
    _ < b * a := mul_lt_mul_left h a

@[to_additive add_lt_of_neg_left]
/-
**mul_lt_of_lt_one_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_of_lt_one_left' [MulRightStrictMono α] (a : α) {b : α} (h : b < 1) 
: b * a < a
参数：a : α；h : b < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_left`：mul_lt_mul_left [i : MulRightStrictMono α] {b c : α} (b
c : b < c) (a : α) : b * a < c * a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem mul_lt_of_lt_one_left' [MulRightStrictMono α] (a : α) {b : α}
    (h : b < 1) :
    b * a < a :=
  calc
    b * a < 1 * a := mul_lt_mul_left h a
    _ = a := one_mul a

@[to_additive]
/-
**one_lt_of_lt_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_lt_of_lt_mul_right [MulLeftReflectLT α] {a b : α} (h : a < a * b) : 1 
< b
参数：h : a < a * b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_mul_lt_mul_left'`：lt_of_mul_lt_mul_left' [MulLeftReflectLT α] {a b
 c : α} (bc : a * b < a * c) : b < c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem one_lt_of_lt_mul_right [MulLeftReflectLT α] {a b : α} (h : a < a * b) :
    1 < b :=
  lt_of_mul_lt_mul_left' (a := a) <| by simpa only [mul_one]

@[to_additive]
/-
**lt_one_of_mul_lt_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_one_of_mul_lt_right [MulLeftReflectLT α] {a b : α} (h : a * b < a) : b 
< 1
参数：h : a * b < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_mul_lt_mul_left'`：lt_of_mul_lt_mul_left' [MulLeftReflectLT α] {a b
 c : α} (bc : a * b < a * c) : b < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem lt_one_of_mul_lt_right [MulLeftReflectLT α] {a b : α} (h : a * b < a) :
    b < 1 :=
  lt_of_mul_lt_mul_left' (a := a) <| by simpa only [mul_one]

@[to_additive]
/-
**one_lt_of_lt_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_lt_of_lt_mul_left [MulRightReflectLT α] {a b : α} (h : b < a * b) : 1 
< a
参数：h : b < a * b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_mul_lt_mul_right'`：lt_of_mul_lt_mul_right' [i : MulRightReflectLT 
α] {a b c : α} (bc : b * a < c * a) : b < c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem one_lt_of_lt_mul_left [MulRightReflectLT α] {a b : α}
    (h : b < a * b) :
    1 < a :=
  lt_of_mul_lt_mul_right' (a := b) <| by simpa only [one_mul]

@[to_additive]
/-
**lt_one_of_mul_lt_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_one_of_mul_lt_left [MulRightReflectLT α] {a b : α} (h : a * b < b) : a 
< 1
参数：h : a * b < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_mul_lt_mul_right'`：lt_of_mul_lt_mul_right' [i : MulRightReflectLT 
α] {a b c : α} (bc : b * a < c * a) : b < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem lt_one_of_mul_lt_left [MulRightReflectLT α] {a b : α}
    (h : a * b < b) :
    a < 1 :=
  lt_of_mul_lt_mul_right' (a := b) <| by simpa only [one_mul]

@[to_additive (attr := simp) lt_add_iff_pos_right]
/-
**lt_mul_iff_one_lt_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_mul_iff_one_lt_right' [MulLeftStrictMono α] [MulLeftReflectLT α] (a : α
) {b : α} : a < a * b ↔ 1 < b
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `mul_lt_mul_iff_left`：mul_lt_mul_iff_left [MulLeftStrictMono α] [MulLeftR
eflectLT α] (a : α) {b c : α} : a * b < a * c ↔ b < c
-/
theorem lt_mul_iff_one_lt_right' [MulLeftStrictMono α]
    [MulLeftReflectLT α] (a : α) {b : α} :
    a < a * b ↔ 1 < b :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_left a)

@[to_additive (attr := simp) lt_add_iff_pos_left]
/-
**lt_mul_iff_one_lt_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_mul_iff_one_lt_left' [MulRightStrictMono α] [MulRightReflectLT α] (a : 
α) {b : α} : a < b * a ↔ 1 < b
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `mul_lt_mul_iff_right`：mul_lt_mul_iff_right [MulRightStrictMono α] [MulRi
ghtReflectLT α] (a : α) {b c : α} : b * a < c * a ↔ b < c
-/
theorem lt_mul_iff_one_lt_left' [MulRightStrictMono α]
    [MulRightReflectLT α] (a : α) {b : α} : a < b * a ↔ 1 < b :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_right a)

@[to_additive (attr := simp) add_lt_iff_neg_left]
/-
**mul_lt_iff_lt_one_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_iff_lt_one_left' [MulLeftStrictMono α] [MulLeftReflectLT α] {a b : 
α} : a * b < a ↔ b < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `mul_lt_mul_iff_left`：mul_lt_mul_iff_left [MulLeftStrictMono α] [MulLeftR
eflectLT α] (a : α) {b c : α} : a * b < a * c ↔ b < c
-/
theorem mul_lt_iff_lt_one_left' [MulLeftStrictMono α]
    [MulLeftReflectLT α] {a b : α} :
    a * b < a ↔ b < 1 :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_left a)

@[to_additive (attr := simp) add_lt_iff_neg_right]
/-
**mul_lt_iff_lt_one_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_iff_lt_one_right' [MulRightStrictMono α] [MulRightReflectLT α] {a :
 α} (b : α) : a * b < b ↔ a < 1
参数：b : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `mul_lt_mul_iff_right`：mul_lt_mul_iff_right [MulRightStrictMono α] [MulRi
ghtReflectLT α] (a : α) {b c : α} : b * a < c * a ↔ b < c
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
/-
**mul_le_of_le_of_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_of_le_of_le_one [MulLeftMono α] {a b c : α} (hbc : b <= c) (ha : a 
<= 1) : b * a <= c
参数：hbc : b <= c；ha : a <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
Lemmas of the form `b ≤ c → a ≤ 1 → b * a ≤ c`,
which assume left covariance.
-/
theorem mul_le_of_le_of_le_one [MulLeftMono α] {a b c : α} (hbc : b ≤ c)
    (ha : a ≤ 1) :
    b * a ≤ c :=
  calc
    b * a ≤ b * 1 := mul_le_mul_right ha b
    _ = b := mul_one b
    _ ≤ c := hbc

@[to_additive]
/-
**mul_lt_of_le_of_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_of_le_of_lt_one [MulLeftStrictMono α] {a b c : α} (hbc : b <= c) (h
a : a < 1) : b * a < c
参数：hbc : b <= c；ha : a < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_right`：mul_lt_mul_right [MulLeftStrictMono α] {b c : α} (bc :
 b < c) (a : α) : a * b < a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mul_lt_of_le_of_lt_one [MulLeftStrictMono α] {a b c : α} (hbc : b ≤ c)
    (ha : a < 1) :
    b * a < c :=
  calc
    b * a < b * 1 := mul_lt_mul_right ha b
    _ = b := mul_one b
    _ ≤ c := hbc

@[to_additive]
/-
**mul_lt_of_lt_of_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_of_lt_of_le_one [MulLeftMono α] {a b c : α} (hbc : b < c) (ha : a <
= 1) : b * a < c
参数：hbc : b < c；ha : a <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mul_lt_of_lt_of_le_one [MulLeftMono α] {a b c : α} (hbc : b < c)
    (ha : a ≤ 1) :
    b * a < c :=
  calc
    b * a ≤ b * 1 := mul_le_mul_right ha b
    _ = b := mul_one b
    _ < c := hbc

@[to_additive]
/-
**mul_lt_of_lt_of_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_of_lt_of_lt_one [MulLeftStrictMono α] {a b c : α} (hbc : b < c) (ha
 : a < 1) : b * a < c
参数：hbc : b < c；ha : a < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_right`：mul_lt_mul_right [MulLeftStrictMono α] {b c : α} (bc :
 b < c) (a : α) : a * b < a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mul_lt_of_lt_of_lt_one [MulLeftStrictMono α] {a b c : α} (hbc : b < c)
    (ha : a < 1) :
    b * a < c :=
  calc
    b * a < b * 1 := mul_lt_mul_right ha b
    _ = b := mul_one b
    _ < c := hbc

@[to_additive]
/-
**mul_lt_of_lt_of_lt_one'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_of_lt_of_lt_one' [MulLeftMono α] {a b c : α} (hbc : b < c) (ha : a 
< 1) : b * a < c
参数：hbc : b < c；ha : a < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_of_lt_of_le_one`：mul_lt_of_lt_of_le_one [MulLeftMono α] {a b c : 
α} (hbc : b < c) (ha : a <= 1) : b * a < c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem mul_lt_of_lt_of_lt_one' [MulLeftMono α] {a b c : α} (hbc : b < c)
    (ha : a < 1) :
    b * a < c :=
  mul_lt_of_lt_of_le_one hbc ha.le

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.mul_le_one`. -/
@[to_additive /-- Assumes left covariance.
The lemma assuming right covariance is `Right.add_nonpos`. -/]
/-
**Left.mul_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Left.mul_le_one [MulLeftMono α] {a b : α} (ha : a <= 1) (hb : b <= 1) : a 
* b <= 1
参数：ha : a <= 1；hb : b <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_of_le_of_le_one`：mul_le_of_le_of_le_one [MulLeftMono α] {a b c : 
α} (hbc : b <= c) (ha : a <= 1) : b * a <= c
-/
theorem Left.mul_le_one [MulLeftMono α] {a b : α} (ha : a ≤ 1) (hb : b ≤ 1) :
    a * b ≤ 1 :=
  mul_le_of_le_of_le_one ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.mul_lt_one_of_le_of_lt`. -/
@[to_additive Left.add_neg_of_nonpos_of_neg
      /-- Assumes left covariance.
      The lemma assuming right covariance is `Right.add_neg_of_nonpos_of_neg`. -/]
/-
**Left.mul_lt_one_of_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Left.mul_lt_one_of_le_of_lt [MulLeftStrictMono α] {a b : α} (ha : a <= 1) 
(hb : b < 1) : a * b < 1
参数：ha : a <= 1；hb : b < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_of_le_of_lt_one`：mul_lt_of_le_of_lt_one [MulLeftStrictMono α] {a 
b c : α} (hbc : b <= c) (ha : a < 1) : b * a < c
-/
theorem Left.mul_lt_one_of_le_of_lt [MulLeftStrictMono α] {a b : α} (ha : a ≤ 1)
    (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_le_of_lt_one ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.mul_lt_one_of_lt_of_le`. -/
@[to_additive Left.add_neg_of_neg_of_nonpos
      /-- Assumes left covariance.
      The lemma assuming right covariance is `Right.add_neg_of_neg_of_nonpos`. -/]
/-
**Left.mul_lt_one_of_lt_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Left.mul_lt_one_of_lt_of_le [MulLeftMono α] {a b : α} (ha : a < 1) (hb : b
 <= 1) : a * b < 1
参数：ha : a < 1；hb : b <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_of_lt_of_le_one`：mul_lt_of_lt_of_le_one [MulLeftMono α] {a b c : 
α} (hbc : b < c) (ha : a <= 1) : b * a < c
-/
theorem Left.mul_lt_one_of_lt_of_le [MulLeftMono α] {a b : α} (ha : a < 1)
    (hb : b ≤ 1) :
    a * b < 1 :=
  mul_lt_of_lt_of_le_one ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.mul_lt_one`. -/
@[to_additive /-- Assumes left covariance.
The lemma assuming right covariance is `Right.add_neg`. -/]
/-
**Left.mul_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Left.mul_lt_one [MulLeftStrictMono α] {a b : α} (ha : a < 1) (hb : b < 1) 
: a * b < 1
参数：ha : a < 1；hb : b < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_of_lt_of_lt_one`：mul_lt_of_lt_of_lt_one [MulLeftStrictMono α] {a 
b c : α} (hbc : b < c) (ha : a < 1) : b * a < c
-/
theorem Left.mul_lt_one [MulLeftStrictMono α] {a b : α} (ha : a < 1) (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_lt_of_lt_one ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.mul_lt_one'`. -/
@[to_additive /-- Assumes left covariance.
The lemma assuming right covariance is `Right.add_neg'`. -/]
/-
**Left.mul_lt_one'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Left.mul_lt_one' [MulLeftMono α] {a b : α} (ha : a < 1) (hb : b < 1) : a *
 b < 1
参数：ha : a < 1；hb : b < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_of_lt_of_lt_one'`：mul_lt_of_lt_of_lt_one' [MulLeftMono α] {a b c 
: α} (hbc : b < c) (ha : a < 1) : b * a < c
-/
theorem Left.mul_lt_one' [MulLeftMono α] {a b : α} (ha : a < 1) (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_lt_of_lt_one' ha hb

/-! Lemmas of the form `b ≤ c → 1 ≤ a → b ≤ c * a`,
which assume left covariance. -/


@[to_additive]
/-
**le_mul_of_le_of_one_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_mul_of_le_of_one_le [MulLeftMono α] {a b c : α} (hbc : b <= c) (ha : 1 
<= a) : b <= c * a
参数：hbc : b <= c；ha : 1 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c

--- 原说明 ---
Lemmas of the form `b ≤ c → 1 ≤ a → b ≤ c * a`,
which assume left covariance.
-/
theorem le_mul_of_le_of_one_le [MulLeftMono α] {a b c : α} (hbc : b ≤ c)
    (ha : 1 ≤ a) :
    b ≤ c * a :=
  calc
    b ≤ c := hbc
    _ = c * 1 := (mul_one c).symm
    _ ≤ c * a := mul_le_mul_right ha c

@[to_additive]
/-
**lt_mul_of_le_of_one_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_mul_of_le_of_one_lt [MulLeftStrictMono α] {a b c : α} (hbc : b <= c) (h
a : 1 < a) : b < c * a
参数：hbc : b <= c；ha : 1 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_lt_mul_right`：mul_lt_mul_right [MulLeftStrictMono α] {b c : α} (bc :
 b < c) (a : α) : a * b < a * c
-/
theorem lt_mul_of_le_of_one_lt [MulLeftStrictMono α] {a b c : α} (hbc : b ≤ c)
    (ha : 1 < a) :
    b < c * a :=
  calc
    b ≤ c := hbc
    _ = c * 1 := (mul_one c).symm
    _ < c * a := mul_lt_mul_right ha c

@[to_additive]
/-
**lt_mul_of_lt_of_one_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_mul_of_lt_of_one_le [MulLeftMono α] {a b c : α} (hbc : b < c) (ha : 1 <
= a) : b < c * a
参数：hbc : b < c；ha : 1 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
-/
theorem lt_mul_of_lt_of_one_le [MulLeftMono α] {a b c : α} (hbc : b < c)
    (ha : 1 ≤ a) :
    b < c * a :=
  calc
    b < c := hbc
    _ = c * 1 := (mul_one c).symm
    _ ≤ c * a := mul_le_mul_right ha c

@[to_additive]
/-
**lt_mul_of_lt_of_one_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_mul_of_lt_of_one_lt [MulLeftStrictMono α] {a b c : α} (hbc : b < c) (ha
 : 1 < a) : b < c * a
参数：hbc : b < c；ha : 1 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_lt_mul_right`：mul_lt_mul_right [MulLeftStrictMono α] {b c : α} (bc :
 b < c) (a : α) : a * b < a * c
-/
theorem lt_mul_of_lt_of_one_lt [MulLeftStrictMono α] {a b c : α} (hbc : b < c)
    (ha : 1 < a) :
    b < c * a :=
  calc
    b < c := hbc
    _ = c * 1 := (mul_one c).symm
    _ < c * a := mul_lt_mul_right ha c

@[to_additive]
/-
**lt_mul_of_lt_of_one_lt'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_mul_of_lt_of_one_lt' [MulLeftMono α] {a b c : α} (hbc : b < c) (ha : 1 
< a) : b < c * a
参数：hbc : b < c；ha : 1 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_mul_of_lt_of_one_le`：lt_mul_of_lt_of_one_le [MulLeftMono α] {a b c : 
α} (hbc : b < c) (ha : 1 <= a) : b < c * a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem lt_mul_of_lt_of_one_lt' [MulLeftMono α] {a b c : α} (hbc : b < c)
    (ha : 1 < a) :
    b < c * a :=
  lt_mul_of_lt_of_one_le hbc ha.le

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.one_le_mul`. -/
@[to_additive Left.add_nonneg /-- Assumes left covariance.
The lemma assuming right covariance is `Right.add_nonneg`. -/]
/-
**Left.one_le_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Left.one_le_mul [MulLeftMono α] {a b : α} (ha : 1 <= a) (hb : 1 <= b) : 1 
<= a * b
参数：ha : 1 <= a；hb : 1 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_mul_of_le_of_one_le`：le_mul_of_le_of_one_le [MulLeftMono α] {a b c : 
α} (hbc : b <= c) (ha : 1 <= a) : b <= c * a
-/
theorem Left.one_le_mul [MulLeftMono α] {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    1 ≤ a * b :=
  le_mul_of_le_of_one_le ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.one_lt_mul_of_le_of_lt`. -/
@[to_additive Left.add_pos_of_nonneg_of_pos
      /-- Assumes left covariance.
      The lemma assuming right covariance is `Right.add_pos_of_nonneg_of_pos`. -/]
/-
**Left.one_lt_mul_of_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Left.one_lt_mul_of_le_of_lt [MulLeftStrictMono α] {a b : α} (ha : 1 <= a) 
(hb : 1 < b) : 1 < a * b
参数：ha : 1 <= a；hb : 1 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_mul_of_le_of_one_lt`：lt_mul_of_le_of_one_lt [MulLeftStrictMono α] {a 
b c : α} (hbc : b <= c) (ha : 1 < a) : b < c * a
-/
theorem Left.one_lt_mul_of_le_of_lt [MulLeftStrictMono α] {a b : α} (ha : 1 ≤ a)
    (hb : 1 < b) :
    1 < a * b :=
  lt_mul_of_le_of_one_lt ha hb

@[to_additive]
/-
**Left.one_lt_mul_of_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Left.one_lt_mul_of_right [IsBotOneClass α] [MulLeftStrictMono α] {b : α} (
hb : 1 < b) (a : α) : 1 < a * b
参数：hb : 1 < b；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Left.one_lt_mul_of_le_of_lt`：Left.one_lt_mul_of_le_of_lt [MulLeftStrictM
ono α] {a b : α} (ha : 1 <= a) (hb : 1 < b) : 1 < a * b
· 使用定理 `one_le`：one_le {a : α} : 1 <= a
-/
theorem Left.one_lt_mul_of_right [IsBotOneClass α] [MulLeftStrictMono α] {b : α}
    (hb : 1 < b) (a : α) : 1 < a * b :=
  Left.one_lt_mul_of_le_of_lt one_le hb

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.one_lt_mul_of_lt_of_le`. -/
@[to_additive Left.add_pos_of_pos_of_nonneg
      /-- Assumes left covariance.
      The lemma assuming right covariance is `Right.add_pos_of_pos_of_nonneg`. -/]
/-
**Left.one_lt_mul_of_lt_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Left.one_lt_mul_of_lt_of_le [MulLeftMono α] {a b : α} (ha : 1 < a) (hb : 1
 <= b) : 1 < a * b
参数：ha : 1 < a；hb : 1 <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_mul_of_lt_of_one_le`：lt_mul_of_lt_of_one_le [MulLeftMono α] {a b c : 
α} (hbc : b < c) (ha : 1 <= a) : b < c * a
-/
theorem Left.one_lt_mul_of_lt_of_le [MulLeftMono α] {a b : α} (ha : 1 < a)
    (hb : 1 ≤ b) :
    1 < a * b :=
  lt_mul_of_lt_of_one_le ha hb

@[to_additive]
/-
**Left.one_lt_mul_of_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Left.one_lt_mul_of_left [IsBotOneClass α] [MulLeftMono α] {a : α} (ha : 1 
< a) (b : α) : 1 < a * b
参数：ha : 1 < a；b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Left.one_lt_mul_of_lt_of_le`：Left.one_lt_mul_of_lt_of_le [MulLeftMono α]
 {a b : α} (ha : 1 < a) (hb : 1 <= b) : 1 < a * b
· 使用定理 `one_le`：one_le {a : α} : 1 <= a
-/
theorem Left.one_lt_mul_of_left [IsBotOneClass α] [MulLeftMono α] {a : α}
    (ha : 1 < a) (b : α) : 1 < a * b :=
  Left.one_lt_mul_of_lt_of_le ha one_le

@[to_additive add_pos_of_left] alias one_lt_mul_of_left := Left.one_lt_mul_of_left

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.one_lt_mul`. -/
@[to_additive Left.add_pos /-- Assumes left covariance.
The lemma assuming right covariance is `Right.add_pos`. -/]
/-
**Left.one_lt_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Left.one_lt_mul [MulLeftStrictMono α] {a b : α} (ha : 1 < a) (hb : 1 < b) 
: 1 < a * b
参数：ha : 1 < a；hb : 1 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_mul_of_lt_of_one_lt`：lt_mul_of_lt_of_one_lt [MulLeftStrictMono α] {a 
b c : α} (hbc : b < c) (ha : 1 < a) : b < c * a
-/
theorem Left.one_lt_mul [MulLeftStrictMono α] {a b : α} (ha : 1 < a) (hb : 1 < b) :
    1 < a * b :=
  lt_mul_of_lt_of_one_lt ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `Right.one_lt_mul'`. -/
@[to_additive Left.add_pos' /-- Assumes left covariance.
The lemma assuming right covariance is `Right.add_pos'`. -/]
/-
**Left.one_lt_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Left.one_lt_mul' [MulLeftMono α] {a b : α} (ha : 1 < a) (hb : 1 < b) : 1 <
 a * b
参数：ha : 1 < a；hb : 1 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_mul_of_lt_of_one_lt'`：lt_mul_of_lt_of_one_lt' [MulLeftMono α] {a b c 
: α} (hbc : b < c) (ha : 1 < a) : b < c * a
-/
theorem Left.one_lt_mul' [MulLeftMono α] {a b : α} (ha : 1 < a) (hb : 1 < b) :
    1 < a * b :=
  lt_mul_of_lt_of_one_lt' ha hb

/-! Lemmas of the form `a ≤ 1 → b ≤ c → a * b ≤ c`,
which assume right covariance. -/


@[to_additive]
/-
**mul_le_of_le_one_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_of_le_one_of_le [MulRightMono α] {a b c : α} (ha : a <= 1) (hbc : b
 <= c) : a * b <= c
参数：ha : a <= 1；hbc : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
Lemmas of the form `a ≤ 1 → b ≤ c → a * b ≤ c`,
which assume right covariance.
-/
theorem mul_le_of_le_one_of_le [MulRightMono α] {a b c : α} (ha : a ≤ 1)
    (hbc : b ≤ c) :
    a * b ≤ c :=
  calc
    a * b ≤ 1 * b := mul_le_mul_left ha b
    _ = b := one_mul b
    _ ≤ c := hbc

@[to_additive]
/-
**mul_lt_of_lt_one_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_of_lt_one_of_le [MulRightStrictMono α] {a b c : α} (ha : a < 1) (hb
c : b <= c) : a * b < c
参数：ha : a < 1；hbc : b <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_left`：mul_lt_mul_left [i : MulRightStrictMono α] {b c : α} (b
c : b < c) (a : α) : b * a < c * a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem mul_lt_of_lt_one_of_le [MulRightStrictMono α] {a b c : α} (ha : a < 1)
    (hbc : b ≤ c) :
    a * b < c :=
  calc
    a * b < 1 * b := mul_lt_mul_left ha b
    _ = b := one_mul b
    _ ≤ c := hbc

@[to_additive]
/-
**mul_lt_of_le_one_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_of_le_one_of_lt [MulRightMono α] {a b c : α} (ha : a <= 1) (hb : b 
< c) : a * b < c
参数：ha : a <= 1；hb : b < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem mul_lt_of_le_one_of_lt [MulRightMono α] {a b c : α} (ha : a ≤ 1)
    (hb : b < c) :
    a * b < c :=
  calc
    a * b ≤ 1 * b := mul_le_mul_left ha b
    _ = b := one_mul b
    _ < c := hb

@[to_additive]
/-
**mul_lt_of_lt_one_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_of_lt_one_of_lt [MulRightStrictMono α] {a b c : α} (ha : a < 1) (hb
 : b < c) : a * b < c
参数：ha : a < 1；hb : b < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_left`：mul_lt_mul_left [i : MulRightStrictMono α] {b c : α} (b
c : b < c) (a : α) : b * a < c * a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem mul_lt_of_lt_one_of_lt [MulRightStrictMono α] {a b c : α} (ha : a < 1)
    (hb : b < c) :
    a * b < c :=
  calc
    a * b < 1 * b := mul_lt_mul_left ha b
    _ = b := one_mul b
    _ < c := hb

@[to_additive]
/-
**mul_lt_of_lt_one_of_lt'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_of_lt_one_of_lt' [MulRightMono α] {a b c : α} (ha : a < 1) (hbc : b
 < c) : a * b < c
参数：ha : a < 1；hbc : b < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_of_le_one_of_lt`：mul_lt_of_le_one_of_lt [MulRightMono α] {a b c :
 α} (ha : a <= 1) (hb : b < c) : a * b < c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem mul_lt_of_lt_one_of_lt' [MulRightMono α] {a b c : α} (ha : a < 1)
    (hbc : b < c) :
    a * b < c :=
  mul_lt_of_le_one_of_lt ha.le hbc

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.mul_le_one`. -/
@[to_additive /-- Assumes right covariance.
The lemma assuming left covariance is `Left.add_nonpos`. -/]
/-
**Right.mul_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.mul_le_one [MulRightMono α] {a b : α} (ha : a <= 1) (hb : b <= 1) : 
a * b <= 1
参数：ha : a <= 1；hb : b <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_of_le_one_of_le`：mul_le_of_le_one_of_le [MulRightMono α] {a b c :
 α} (ha : a <= 1) (hbc : b <= c) : a * b <= c
-/
theorem Right.mul_le_one [MulRightMono α] {a b : α} (ha : a ≤ 1)
    (hb : b ≤ 1) :
    a * b ≤ 1 :=
  mul_le_of_le_one_of_le ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.mul_lt_one_of_lt_of_le`. -/
@[to_additive Right.add_neg_of_neg_of_nonpos
      /-- Assumes right covariance.
      The lemma assuming left covariance is `Left.add_neg_of_neg_of_nonpos`. -/]
/-
**Right.mul_lt_one_of_lt_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.mul_lt_one_of_lt_of_le [MulRightStrictMono α] {a b : α} (ha : a < 1)
 (hb : b <= 1) : a * b < 1
参数：ha : a < 1；hb : b <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_of_lt_one_of_le`：mul_lt_of_lt_one_of_le [MulRightStrictMono α] {a
 b c : α} (ha : a < 1) (hbc : b <= c) : a * b < c
-/
theorem Right.mul_lt_one_of_lt_of_le [MulRightStrictMono α] {a b : α}
    (ha : a < 1) (hb : b ≤ 1) :
    a * b < 1 :=
  mul_lt_of_lt_one_of_le ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.mul_lt_one_of_le_of_lt`. -/
@[to_additive Right.add_neg_of_nonpos_of_neg
      /-- Assumes right covariance.
      The lemma assuming left covariance is `Left.add_neg_of_nonpos_of_neg`. -/]
/-
**Right.mul_lt_one_of_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.mul_lt_one_of_le_of_lt [MulRightMono α] {a b : α} (ha : a <= 1) (hb 
: b < 1) : a * b < 1
参数：ha : a <= 1；hb : b < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_of_le_one_of_lt`：mul_lt_of_le_one_of_lt [MulRightMono α] {a b c :
 α} (ha : a <= 1) (hb : b < c) : a * b < c
-/
theorem Right.mul_lt_one_of_le_of_lt [MulRightMono α] {a b : α}
    (ha : a ≤ 1) (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_le_one_of_lt ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.mul_lt_one`. -/
@[to_additive /-- Assumes right covariance.
The lemma assuming left covariance is `Left.add_neg`. -/]
/-
**Right.mul_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.mul_lt_one [MulRightStrictMono α] {a b : α} (ha : a < 1) (hb : b < 1
) : a * b < 1
参数：ha : a < 1；hb : b < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_of_lt_one_of_lt`：mul_lt_of_lt_one_of_lt [MulRightStrictMono α] {a
 b c : α} (ha : a < 1) (hb : b < c) : a * b < c
-/
theorem Right.mul_lt_one [MulRightStrictMono α] {a b : α} (ha : a < 1)
    (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_lt_one_of_lt ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.mul_lt_one'`. -/
@[to_additive /-- Assumes right covariance.
The lemma assuming left covariance is `Left.add_neg'`. -/]
/-
**Right.mul_lt_one'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.mul_lt_one' [MulRightMono α] {a b : α} (ha : a < 1) (hb : b < 1) : a
 * b < 1
参数：ha : a < 1；hb : b < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_of_lt_one_of_lt'`：mul_lt_of_lt_one_of_lt' [MulRightMono α] {a b c
 : α} (ha : a < 1) (hbc : b < c) : a * b < c
-/
theorem Right.mul_lt_one' [MulRightMono α] {a b : α} (ha : a < 1)
    (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_lt_one_of_lt' ha hb

/-! Lemmas of the form `1 ≤ a → b ≤ c → b ≤ a * c`,
which assume right covariance. -/


@[to_additive]
/-
**le_mul_of_one_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_mul_of_one_le_of_le [MulRightMono α] {a b c : α} (ha : 1 <= a) (hbc : b
 <= c) : b <= a * c
参数：ha : 1 <= a；hbc : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a

--- 原说明 ---
Lemmas of the form `1 ≤ a → b ≤ c → b ≤ a * c`,
which assume right covariance.
-/
theorem le_mul_of_one_le_of_le [MulRightMono α] {a b c : α} (ha : 1 ≤ a)
    (hbc : b ≤ c) :
    b ≤ a * c :=
  calc
    b ≤ c := hbc
    _ = 1 * c := (one_mul c).symm
    _ ≤ a * c := mul_le_mul_left ha c

@[to_additive]
/-
**lt_mul_of_one_lt_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_mul_of_one_lt_of_le [MulRightStrictMono α] {a b c : α} (ha : 1 < a) (hb
c : b <= c) : b < a * c
参数：ha : 1 < a；hbc : b <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_lt_mul_left`：mul_lt_mul_left [i : MulRightStrictMono α] {b c : α} (b
c : b < c) (a : α) : b * a < c * a
-/
theorem lt_mul_of_one_lt_of_le [MulRightStrictMono α] {a b c : α} (ha : 1 < a)
    (hbc : b ≤ c) :
    b < a * c :=
  calc
    b ≤ c := hbc
    _ = 1 * c := (one_mul c).symm
    _ < a * c := mul_lt_mul_left ha c

@[to_additive]
/-
**lt_mul_of_one_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_mul_of_one_le_of_lt [MulRightMono α] {a b c : α} (ha : 1 <= a) (hbc : b
 < c) : b < a * c
参数：ha : 1 <= a；hbc : b < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
-/
theorem lt_mul_of_one_le_of_lt [MulRightMono α] {a b c : α} (ha : 1 ≤ a)
    (hbc : b < c) :
    b < a * c :=
  calc
    b < c := hbc
    _ = 1 * c := (one_mul c).symm
    _ ≤ a * c := mul_le_mul_left ha c

@[to_additive]
/-
**lt_mul_of_one_lt_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_mul_of_one_lt_of_lt [MulRightStrictMono α] {a b c : α} (ha : 1 < a) (hb
c : b < c) : b < a * c
参数：ha : 1 < a；hbc : b < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_lt_mul_left`：mul_lt_mul_left [i : MulRightStrictMono α] {b c : α} (b
c : b < c) (a : α) : b * a < c * a
-/
theorem lt_mul_of_one_lt_of_lt [MulRightStrictMono α] {a b c : α} (ha : 1 < a)
    (hbc : b < c) :
    b < a * c :=
  calc
    b < c := hbc
    _ = 1 * c := (one_mul c).symm
    _ < a * c := mul_lt_mul_left ha c

@[to_additive]
/-
**lt_mul_of_one_lt_of_lt'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_mul_of_one_lt_of_lt' [MulRightMono α] {a b c : α} (ha : 1 < a) (hbc : b
 < c) : b < a * c
参数：ha : 1 < a；hbc : b < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_mul_of_one_le_of_lt`：lt_mul_of_one_le_of_lt [MulRightMono α] {a b c :
 α} (ha : 1 <= a) (hbc : b < c) : b < a * c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem lt_mul_of_one_lt_of_lt' [MulRightMono α] {a b c : α} (ha : 1 < a)
    (hbc : b < c) :
    b < a * c :=
  lt_mul_of_one_le_of_lt ha.le hbc

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.one_le_mul`. -/
@[to_additive Right.add_nonneg /-- Assumes right covariance.
The lemma assuming left covariance is `Left.add_nonneg`. -/]
/-
**Right.one_le_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.one_le_mul [MulRightMono α] {a b : α} (ha : 1 <= a) (hb : 1 <= b) : 
1 <= a * b
参数：ha : 1 <= a；hb : 1 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_mul_of_one_le_of_le`：le_mul_of_one_le_of_le [MulRightMono α] {a b c :
 α} (ha : 1 <= a) (hbc : b <= c) : b <= a * c
-/
theorem Right.one_le_mul [MulRightMono α] {a b : α} (ha : 1 ≤ a)
    (hb : 1 ≤ b) :
    1 ≤ a * b :=
  le_mul_of_one_le_of_le ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.one_lt_mul_of_lt_of_le`. -/
@[to_additive Right.add_pos_of_pos_of_nonneg
/-- Assumes right covariance.
The lemma assuming left covariance is `Left.add_pos_of_pos_of_nonneg`. -/]
/-
**Right.one_lt_mul_of_lt_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.one_lt_mul_of_lt_of_le [MulRightStrictMono α] {a b : α} (ha : 1 < a)
 (hb : 1 <= b) : 1 < a * b
参数：ha : 1 < a；hb : 1 <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_mul_of_one_lt_of_le`：lt_mul_of_one_lt_of_le [MulRightStrictMono α] {a
 b c : α} (ha : 1 < a) (hbc : b <= c) : b < a * c
-/
theorem Right.one_lt_mul_of_lt_of_le [MulRightStrictMono α] {a b : α}
    (ha : 1 < a) (hb : 1 ≤ b) :
    1 < a * b :=
  lt_mul_of_one_lt_of_le ha hb

@[to_additive]
/-
**Right.one_lt_mul_of_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.one_lt_mul_of_left [IsBotOneClass α] [MulRightStrictMono α] {a : α} 
(ha : 1 < a) (b : α) : 1 < a * b
参数：ha : 1 < a；b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Right.one_lt_mul_of_lt_of_le`：Right.one_lt_mul_of_lt_of_le [MulRightStri
ctMono α] {a b : α} (ha : 1 < a) (hb : 1 <= b) : 1 < a * b
· 使用定理 `one_le`：one_le {a : α} : 1 <= a
-/
theorem Right.one_lt_mul_of_left [IsBotOneClass α] [MulRightStrictMono α] {a : α}
    (ha : 1 < a) (b : α) : 1 < a * b :=
  Right.one_lt_mul_of_lt_of_le ha one_le

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.one_lt_mul_of_le_of_lt`. -/
@[to_additive Right.add_pos_of_nonneg_of_pos
/-- Assumes right covariance.
The lemma assuming left covariance is `Left.add_pos_of_nonneg_of_pos`. -/]
/-
**Right.one_lt_mul_of_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.one_lt_mul_of_le_of_lt [MulRightMono α] {a b : α} (ha : 1 <= a) (hb 
: 1 < b) : 1 < a * b
参数：ha : 1 <= a；hb : 1 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_mul_of_one_le_of_lt`：lt_mul_of_one_le_of_lt [MulRightMono α] {a b c :
 α} (ha : 1 <= a) (hbc : b < c) : b < a * c
-/
theorem Right.one_lt_mul_of_le_of_lt [MulRightMono α] {a b : α}
    (ha : 1 ≤ a) (hb : 1 < b) :
    1 < a * b :=
  lt_mul_of_one_le_of_lt ha hb

@[to_additive]
/-
**Right.one_lt_mul_of_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.one_lt_mul_of_right [IsBotOneClass α] [MulRightMono α] {b : α} (hb :
 1 < b) (a : α) : 1 < a * b
参数：hb : 1 < b；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Right.one_lt_mul_of_le_of_lt`：Right.one_lt_mul_of_le_of_lt [MulRightMono
 α] {a b : α} (ha : 1 <= a) (hb : 1 < b) : 1 < a * b
· 使用定理 `one_le`：one_le {a : α} : 1 <= a
-/
theorem Right.one_lt_mul_of_right [IsBotOneClass α] [MulRightMono α] {b : α}
    (hb : 1 < b) (a : α) : 1 < a * b :=
  Right.one_lt_mul_of_le_of_lt one_le hb

@[to_additive add_pos_of_right] alias one_lt_mul_of_right := Right.one_lt_mul_of_right

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.one_lt_mul`. -/
@[to_additive Right.add_pos /-- Assumes right covariance.
The lemma assuming left covariance is `Left.add_pos`. -/]
/-
**Right.one_lt_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.one_lt_mul [MulRightStrictMono α] {a b : α} (ha : 1 < a) (hb : 1 < b
) : 1 < a * b
参数：ha : 1 < a；hb : 1 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_mul_of_one_lt_of_lt`：lt_mul_of_one_lt_of_lt [MulRightStrictMono α] {a
 b c : α} (ha : 1 < a) (hbc : b < c) : b < a * c
-/
theorem Right.one_lt_mul [MulRightStrictMono α] {a b : α} (ha : 1 < a)
    (hb : 1 < b) :
    1 < a * b :=
  lt_mul_of_one_lt_of_lt ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `Left.one_lt_mul'`. -/
@[to_additive Right.add_pos' /-- Assumes right covariance.
The lemma assuming left covariance is `Left.add_pos'`. -/]
/-
**Right.one_lt_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.one_lt_mul' [MulRightMono α] {a b : α} (ha : 1 < a) (hb : 1 < b) : 1
 < a * b
参数：ha : 1 < a；hb : 1 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_mul_of_one_lt_of_lt'`：lt_mul_of_one_lt_of_lt' [MulRightMono α] {a b c
 : α} (ha : 1 < a) (hbc : b < c) : b < a * c
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
/-
**lt_of_mul_lt_of_one_le_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_of_mul_lt_of_one_le_left [MulLeftMono α] {a b c : α} (h : a * b < c) (h
le : 1 <= b) : a < c
参数：h : a * b < c；hle : 1 <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `le_mul_of_one_le_right'`：le_mul_of_one_le_right' [MulLeftMono α] {a b : 
α} (h : 1 <= b) : a <= a * b
-/
theorem lt_of_mul_lt_of_one_le_left [MulLeftMono α] {a b c : α} (h : a * b < c)
    (hle : 1 ≤ b) :
    a < c :=
  (le_mul_of_one_le_right' hle).trans_lt h

@[to_additive]
/-
**le_of_mul_le_of_one_le_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_mul_le_of_one_le_left [MulLeftMono α] {a b c : α} (h : a * b <= c) (
hle : 1 <= b) : a <= c
参数：h : a * b <= c；hle : 1 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_mul_of_one_le_right'`：le_mul_of_one_le_right' [MulLeftMono α] {a b : 
α} (h : 1 <= b) : a <= a * b
-/
theorem le_of_mul_le_of_one_le_left [MulLeftMono α] {a b c : α} (h : a * b ≤ c)
    (hle : 1 ≤ b) :
    a ≤ c :=
  (le_mul_of_one_le_right' hle).trans h

@[to_additive]
/-
**lt_of_lt_mul_of_le_one_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_of_lt_mul_of_le_one_left [MulLeftMono α] {a b c : α} (h : a < b * c) (h
le : c <= 1) : a < b
参数：h : a < b * c；hle : c <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `mul_le_of_le_one_right'`：mul_le_of_le_one_right' [MulLeftMono α] {a b : 
α} (h : b <= 1) : a * b <= a
-/
theorem lt_of_lt_mul_of_le_one_left [MulLeftMono α] {a b c : α} (h : a < b * c)
    (hle : c ≤ 1) :
    a < b :=
  h.trans_le (mul_le_of_le_one_right' hle)

@[to_additive]
/-
**le_of_le_mul_of_le_one_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_le_mul_of_le_one_left [MulLeftMono α] {a b c : α} (h : a <= b * c) (
hle : c <= 1) : a <= b
参数：h : a <= b * c；hle : c <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_of_le_one_right'`：mul_le_of_le_one_right' [MulLeftMono α] {a b : 
α} (h : b <= 1) : a * b <= a
-/
theorem le_of_le_mul_of_le_one_left [MulLeftMono α] {a b c : α} (h : a ≤ b * c)
    (hle : c ≤ 1) :
    a ≤ b :=
  h.trans (mul_le_of_le_one_right' hle)

@[to_additive]
/-
**lt_of_mul_lt_of_one_le_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_of_mul_lt_of_one_le_right [MulRightMono α] {a b c : α} (h : a * b < c) 
(hle : 1 <= a) : b < c
参数：h : a * b < c；hle : 1 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `le_mul_of_one_le_left'`：le_mul_of_one_le_left' [MulRightMono α] {a b : α
} (h : 1 <= b) : a <= b * a
-/
theorem lt_of_mul_lt_of_one_le_right [MulRightMono α] {a b c : α}
    (h : a * b < c) (hle : 1 ≤ a) :
    b < c :=
  (le_mul_of_one_le_left' hle).trans_lt h

@[to_additive]
/-
**le_of_mul_le_of_one_le_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_mul_le_of_one_le_right [MulRightMono α] {a b c : α} (h : a * b <= c)
 (hle : 1 <= a) : b <= c
参数：h : a * b <= c；hle : 1 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_mul_of_one_le_left'`：le_mul_of_one_le_left' [MulRightMono α] {a b : α
} (h : 1 <= b) : a <= b * a
-/
theorem le_of_mul_le_of_one_le_right [MulRightMono α] {a b c : α}
    (h : a * b ≤ c) (hle : 1 ≤ a) :
    b ≤ c :=
  (le_mul_of_one_le_left' hle).trans h

@[to_additive]
/-
**lt_of_lt_mul_of_le_one_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_of_lt_mul_of_le_one_right [MulRightMono α] {a b c : α} (h : a < b * c) 
(hle : b <= 1) : a < c
参数：h : a < b * c；hle : b <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `mul_le_of_le_one_left'`：mul_le_of_le_one_left' [MulRightMono α] {a b : α
} (h : b <= 1) : b * a <= a
-/
theorem lt_of_lt_mul_of_le_one_right [MulRightMono α] {a b c : α}
    (h : a < b * c) (hle : b ≤ 1) :
    a < c :=
  h.trans_le (mul_le_of_le_one_left' hle)

@[to_additive]
/-
**le_of_le_mul_of_le_one_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_le_mul_of_le_one_right [MulRightMono α] {a b c : α} (h : a <= b * c)
 (hle : b <= 1) : a <= c
参数：h : a <= b * c；hle : b <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_of_le_one_left'`：mul_le_of_le_one_left' [MulRightMono α] {a b : α
} (h : b <= 1) : b * a <= a
-/
theorem le_of_le_mul_of_le_one_right [MulRightMono α] {a b c : α}
    (h : a ≤ b * c) (hle : b ≤ 1) :
    a ≤ c :=
  h.trans (mul_le_of_le_one_left' hle)

end Preorder

section PartialOrder

variable [PartialOrder α]

@[to_additive]
/-
**mul_eq_one_iff_of_one_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_eq_one_iff_of_one_le [MulLeftMono α] [MulRightMono α] {a b : α} (ha : 
1 <= a) (hb : 1 <= b) : a * b = 1 ↔ a = 1 ∧ b = 1
参数：ha : 1 <= a；hb : 1 <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_mul_of_le_of_one_le`：le_mul_of_le_of_one_le [MulLeftMono α] {a b c : 
α} (hbc : b <= c) (ha : 1 <= a) : b <= c * a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_mul_of_one_le_of_le`：le_mul_of_one_le_of_le [MulRightMono α] {a b c :
 α} (ha : 1 <= a) (hbc : b <= c) : b <= a * c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mul_eq_one_iff_of_one_le [MulLeftMono α]
    [MulRightMono α] {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    a * b = 1 ↔ a = 1 ∧ b = 1 :=
  Iff.intro
    (fun hab : a * b = 1 =>
      have : a ≤ 1 := hab ▸ le_mul_of_le_of_one_le le_rfl hb
      have : a = 1 := le_antisymm this ha
      have : b ≤ 1 := hab ▸ le_mul_of_one_le_of_le ha le_rfl
      have : b = 1 := le_antisymm this hb
      And.intro ‹a = 1› ‹b = 1›)
    (by rintro ⟨rfl, rfl⟩; rw [mul_one])

section Left

variable [MulLeftMono α] {a b : α}

@[to_additive eq_zero_of_add_nonneg_left]
/-
**eq_one_of_one_le_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_one_of_one_le_mul_left (ha : a <= 1) (hb : b <= 1) (hab : 1 <= a * b) :
 a = 1
参数：ha : a <= 1；hb : b <= 1；hab : 1 <= a * b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_of_not_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, 
a ≤ b → ¬a < b → a = b
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `mul_lt_one_of_lt_of_le`：∀ {α : Type u_1} [inst : MulOneClass α] [inst_1 
: Preorder α] [MulLeftMono α] {a b : α}, a < 1 → b ≤ 1 → a * b < 1
-/
theorem eq_one_of_one_le_mul_left (ha : a ≤ 1) (hb : b ≤ 1) (hab : 1 ≤ a * b) : a = 1 :=
  ha.eq_of_not_lt fun h => hab.not_gt <| mul_lt_one_of_lt_of_le h hb

@[to_additive]
/-
**eq_one_of_mul_le_one_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_one_of_mul_le_one_left (ha : 1 <= a) (hb : 1 <= b) (hab : a * b <= 1) :
 a = 1
参数：ha : 1 <= a；hb : 1 <= b；hab : a * b <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_of_not_lt'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 b ≤ a → ¬b < a → a = b
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `one_lt_mul_of_lt_of_le'`：∀ {α : Type u_1} [inst : MulOneClass α] [inst_1
 : Preorder α] [MulLeftMono α] {a b : α}, 1 < a → 1 ≤ b → 1 < a * b
-/
theorem eq_one_of_mul_le_one_left (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b ≤ 1) : a = 1 :=
  ha.eq_of_not_lt' fun h => hab.not_gt <| one_lt_mul_of_lt_of_le' h hb

end Left

section Right

variable [MulRightMono α] {a b : α}

@[to_additive eq_zero_of_add_nonneg_right]
/-
**eq_one_of_one_le_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_one_of_one_le_mul_right (ha : a <= 1) (hb : b <= 1) (hab : 1 <= a * b) 
: b = 1
参数：ha : a <= 1；hb : b <= 1；hab : 1 <= a * b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_of_not_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, 
a ≤ b → ¬a < b → a = b
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Right.mul_lt_one_of_le_of_lt`：Right.mul_lt_one_of_le_of_lt [MulRightMono
 α] {a b : α} (ha : a <= 1) (hb : b < 1) : a * b < 1
-/
theorem eq_one_of_one_le_mul_right (ha : a ≤ 1) (hb : b ≤ 1) (hab : 1 ≤ a * b) : b = 1 :=
  hb.eq_of_not_lt fun h => hab.not_gt <| Right.mul_lt_one_of_le_of_lt ha h

@[to_additive]
/-
**eq_one_of_mul_le_one_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_one_of_mul_le_one_right (ha : 1 <= a) (hb : 1 <= b) (hab : a * b <= 1) 
: b = 1
参数：ha : 1 <= a；hb : 1 <= b；hab : a * b <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_of_not_lt'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 b ≤ a → ¬b < a → a = b
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Right.one_lt_mul_of_le_of_lt`：Right.one_lt_mul_of_le_of_lt [MulRightMono
 α] {a b : α} (ha : 1 <= a) (hb : 1 < b) : 1 < a * b
-/
theorem eq_one_of_mul_le_one_right (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b ≤ 1) : b = 1 :=
  hb.eq_of_not_lt' fun h => hab.not_gt <| Right.one_lt_mul_of_le_of_lt ha h

end Right

end PartialOrder

section LinearOrder

variable [LinearOrder α]

/-
**exists_square_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_square_le [MulLeftStrictMono α] (a : α) : exists b : α, b * b <= a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_right`：mul_lt_mul_right [MulLeftStrictMono α] {b c : α} (bc :
 b < c) (a : α) : a * b < a * c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem exists_square_le [MulLeftStrictMono α] (a : α) : ∃ b : α, b * b ≤ a := by
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
/-
**Contravariant.toLeftCancelSemigroup** 是 Mathlib 中的一个定义，位于命名空间 `Contravariant`。
形式化陈述：{α : Type u_1} → [inst : Semigroup α] → [inst_1 : PartialOrder α] → [MulLe
ftReflectLE α] → LeftCancelSemigroup α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Contravariant.toLeftCancelSemigroup [MulLeftReflectLE α] : LeftCancelSemigroup α where

/- This is not instance, since we want to have an instance from `RightCancelSemigroup`s
to the appropriate covariant class. -/
/-- A semigroup with a partial order and satisfying `RightCancelSemigroup`
(i.e. `a * c < b * c → a < b`) is a `RightCancelSemigroup`. -/
@[to_additive (attr := instance_reducible)
/-- An additive semigroup with a partial order and satisfying `AddRightCancelSemigroup`
(`a + c < b + c → a < b`) is a `AddRightCancelSemigroup`. -/]
/-
**Contravariant.toRightCancelSemigroup** 是 Mathlib 中的一个定义，位于命名空间 `Contravariant`
。
形式化陈述：{α : Type u_1} → [inst : Semigroup α] → [inst_1 : PartialOrder α] → [MulRi
ghtReflectLE α] → RightCancelSemigroup α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Contravariant.toRightCancelSemigroup [MulRightReflectLE α] : RightCancelSemigroup α where

end PartialOrder

end Semigroup

section Mono

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

@[to_additive const_add]
/-
**Monotone.const_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.const_mul' [MulLeftMono α] (hf : Monotone f) (a : α) : Monotone f
un x => a * f x
参数：hf : Monotone f；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用引理 `mul_right_mono`：mul_right_mono [MulLeftMono α] {a : α} : Monotone (a * ·
)
-/
theorem Monotone.const_mul' [MulLeftMono α] (hf : Monotone f) (a : α) : Monotone fun x ↦ a * f x :=
  mul_right_mono.comp hf

@[to_additive const_add]
/-
**MonotoneOn.const_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.const_mul' [MulLeftMono α] (hf : MonotoneOn f s) (a : α) : Mono
toneOn (fun x => a * f x) s
参数：hf : MonotoneOn f s；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp_monotoneOn`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α 
→ β} {s : Set …
· 使用引理 `mul_right_mono`：mul_right_mono [MulLeftMono α] {a : α} : Monotone (a * ·
)
-/
theorem MonotoneOn.const_mul' [MulLeftMono α] (hf : MonotoneOn f s) (a : α) :
    MonotoneOn (fun x => a * f x) s := mul_right_mono.comp_monotoneOn hf

@[to_additive const_add]
/-
**Antitone.const_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.const_mul' [MulLeftMono α] (hf : Antitone f) (a : α) : Antitone f
un x => a * f x
参数：hf : Antitone f；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp_antitone`：Monotone.comp_antitone (hg : Monotone g) (hf : A
ntitone f) : Antitone (g ∘ f)
· 使用引理 `mul_right_mono`：mul_right_mono [MulLeftMono α] {a : α} : Monotone (a * ·
)
-/
theorem Antitone.const_mul' [MulLeftMono α] (hf : Antitone f) (a : α) : Antitone fun x ↦ a * f x :=
  mul_right_mono.comp_antitone hf

@[to_additive const_add]
/-
**AntitoneOn.const_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.const_mul' [MulLeftMono α] (hf : AntitoneOn f s) (a : α) : Anti
toneOn (fun x => a * f x) s
参数：hf : AntitoneOn f s；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp_antitoneOn`：Monotone.comp_antitoneOn (hg : Monotone g) (hf
 : AntitoneOn f s) : AntitoneOn (g ∘ f) s
· 使用引理 `mul_right_mono`：mul_right_mono [MulLeftMono α] {a : α} : Monotone (a * ·
)
-/
theorem AntitoneOn.const_mul' [MulLeftMono α] (hf : AntitoneOn f s) (a : α) :
    AntitoneOn (fun x => a * f x) s := mul_right_mono.comp_antitoneOn hf

@[to_additive add_const]
/-
**Monotone.mul_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.mul_const' [MulRightMono α] (hf : Monotone f) (a : α) : Monotone 
fun x => f x * a
参数：hf : Monotone f；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用引理 `mul_left_mono`：mul_left_mono [MulRightMono α] {a : α} : Monotone (· * a)
-/
theorem Monotone.mul_const' [MulRightMono α] (hf : Monotone f) (a : α) :
    Monotone fun x => f x * a := mul_left_mono.comp hf

@[to_additive add_const]
/-
**MonotoneOn.mul_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.mul_const' [MulRightMono α] (hf : MonotoneOn f s) (a : α) : Mon
otoneOn (fun x => f x * a) s
参数：hf : MonotoneOn f s；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp_monotoneOn`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α 
→ β} {s : Set …
· 使用引理 `mul_left_mono`：mul_left_mono [MulRightMono α] {a : α} : Monotone (· * a)
-/
theorem MonotoneOn.mul_const' [MulRightMono α] (hf : MonotoneOn f s) (a : α) :
    MonotoneOn (fun x => f x * a) s := mul_left_mono.comp_monotoneOn hf

@[to_additive add_const]
/-
**Antitone.mul_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.mul_const' [MulRightMono α] (hf : Antitone f) (a : α) : Antitone 
fun x => f x * a
参数：hf : Antitone f；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp_antitone`：Monotone.comp_antitone (hg : Monotone g) (hf : A
ntitone f) : Antitone (g ∘ f)
· 使用引理 `mul_left_mono`：mul_left_mono [MulRightMono α] {a : α} : Monotone (· * a)
-/
theorem Antitone.mul_const' [MulRightMono α] (hf : Antitone f) (a : α) : Antitone fun x ↦ f x * a :=
  mul_left_mono.comp_antitone hf

@[to_additive add_const]
/-
**AntitoneOn.mul_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.mul_const' [MulRightMono α] (hf : AntitoneOn f s) (a : α) : Ant
itoneOn (fun x => f x * a) s
参数：hf : AntitoneOn f s；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp_antitoneOn`：Monotone.comp_antitoneOn (hg : Monotone g) (hf
 : AntitoneOn f s) : AntitoneOn (g ∘ f) s
· 使用引理 `mul_left_mono`：mul_left_mono [MulRightMono α] {a : α} : Monotone (· * a)
-/
theorem AntitoneOn.mul_const' [MulRightMono α] (hf : AntitoneOn f s) (a : α) :
    AntitoneOn (fun x => f x * a) s := mul_left_mono.comp_antitoneOn hf

/-- The product of two monotone functions is monotone. -/
@[to_additive add /-- The sum of two monotone functions is monotone. -/]
/-
**Monotone.mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.mul' [MulLeftMono α] [MulRightMono α] (hf : Monotone f) (hg : Mon
otone g) : Monotone fun x => f x * g x
参数：hf : Monotone f；hg : Monotone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d

--- 原说明 ---
The product of two monotone functions is monotone.
-/
theorem Monotone.mul' [MulLeftMono α]
    [MulRightMono α] (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x * g x := fun _ _ h => mul_le_mul' (hf h) (hg h)

/-- The product of two monotone functions is monotone. -/
@[to_additive add /-- The sum of two monotone functions is monotone. -/]
/-
**MonotoneOn.mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.mul' [MulLeftMono α] [MulRightMono α] (hf : MonotoneOn f s) (hg
 : MonotoneOn g s) : MonotoneOn (fun x => f x * g x) s
参数：hf : MonotoneOn f s；hg : MonotoneOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d

--- 原说明 ---
The product of two monotone functions is monotone.
-/
theorem MonotoneOn.mul' [MulLeftMono α]
    [MulRightMono α] (hf : MonotoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => f x * g x) s := fun _ hx _ hy h =>
  mul_le_mul' (hf hx hy h) (hg hx hy h)

/-- The product of two antitone functions is antitone. -/
@[to_additive add /-- The sum of two antitone functions is antitone. -/]
/-
**Antitone.mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.mul' [MulLeftMono α] [MulRightMono α] (hf : Antitone f) (hg : Ant
itone g) : Antitone fun x => f x * g x
参数：hf : Antitone f；hg : Antitone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d

--- 原说明 ---
The product of two antitone functions is antitone.
-/
theorem Antitone.mul' [MulLeftMono α]
    [MulRightMono α] (hf : Antitone f) (hg : Antitone g) :
    Antitone fun x => f x * g x := fun _ _ h => mul_le_mul' (hf h) (hg h)

/-- The product of two antitone functions is antitone. -/
@[to_additive add /-- The sum of two antitone functions is antitone. -/]
/-
**AntitoneOn.mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.mul' [MulLeftMono α] [MulRightMono α] (hf : AntitoneOn f s) (hg
 : AntitoneOn g s) : AntitoneOn (fun x => f x * g x) s
参数：hf : AntitoneOn f s；hg : AntitoneOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d

--- 原说明 ---
The product of two antitone functions is antitone.
-/
theorem AntitoneOn.mul' [MulLeftMono α]
    [MulRightMono α] (hf : AntitoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => f x * g x) s :=
  fun _ hx _ hy h => mul_le_mul' (hf hx hy h) (hg hx hy h)

section Left

variable [MulLeftStrictMono α]

@[to_additive const_add]
/-
**StrictMono.const_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.const_mul' (hf : StrictMono f) (c : α) : StrictMono fun x => c 
* f x
参数：hf : StrictMono f；c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_right`：mul_lt_mul_right [MulLeftStrictMono α] {b c : α} (bc :
 b < c) (a : α) : a * b < a * c
-/
theorem StrictMono.const_mul' (hf : StrictMono f) (c : α) : StrictMono fun x => c * f x :=
  fun _ _ ab => mul_lt_mul_right (hf ab) c

@[to_additive const_add]
/-
**StrictMonoOn.const_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMonoOn.const_mul' (hf : StrictMonoOn f s) (c : α) : StrictMonoOn (fu
n x => c * f x) s
参数：hf : StrictMonoOn f s；c : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_right`：mul_lt_mul_right [MulLeftStrictMono α] {b c : α} (bc :
 b < c) (a : α) : a * b < a * c
-/
theorem StrictMonoOn.const_mul' (hf : StrictMonoOn f s) (c : α) :
    StrictMonoOn (fun x => c * f x) s :=
  fun _ ha _ hb ab => mul_lt_mul_right (hf ha hb ab) c

@[to_additive const_add]
/-
**StrictAnti.const_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAnti.const_mul' (hf : StrictAnti f) (c : α) : StrictAnti fun x => c 
* f x
参数：hf : StrictAnti f；c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_right`：mul_lt_mul_right [MulLeftStrictMono α] {b c : α} (bc :
 b < c) (a : α) : a * b < a * c
-/
theorem StrictAnti.const_mul' (hf : StrictAnti f) (c : α) : StrictAnti fun x => c * f x :=
  fun _ _ ab => mul_lt_mul_right (hf ab) c

@[to_additive const_add]
/-
**StrictAntiOn.const_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAntiOn.const_mul' (hf : StrictAntiOn f s) (c : α) : StrictAntiOn (fu
n x => c * f x) s
参数：hf : StrictAntiOn f s；c : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_right`：mul_lt_mul_right [MulLeftStrictMono α] {b c : α} (bc :
 b < c) (a : α) : a * b < a * c
-/
theorem StrictAntiOn.const_mul' (hf : StrictAntiOn f s) (c : α) :
    StrictAntiOn (fun x => c * f x) s :=
  fun _ ha _ hb ab => mul_lt_mul_right (hf ha hb ab) c

end Left

section Right

variable [MulRightStrictMono α]

@[to_additive add_const]
/-
**StrictMono.mul_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.mul_const' (hf : StrictMono f) (c : α) : StrictMono fun x => f 
x * c
参数：hf : StrictMono f；c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_left`：mul_lt_mul_left [i : MulRightStrictMono α] {b c : α} (b
c : b < c) (a : α) : b * a < c * a
-/
theorem StrictMono.mul_const' (hf : StrictMono f) (c : α) : StrictMono fun x => f x * c :=
  fun _ _ ab => mul_lt_mul_left (hf ab) c

@[to_additive add_const]
/-
**StrictMonoOn.mul_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMonoOn.mul_const' (hf : StrictMonoOn f s) (c : α) : StrictMonoOn (fu
n x => f x * c) s
参数：hf : StrictMonoOn f s；c : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_left`：mul_lt_mul_left [i : MulRightStrictMono α] {b c : α} (b
c : b < c) (a : α) : b * a < c * a
-/
theorem StrictMonoOn.mul_const' (hf : StrictMonoOn f s) (c : α) :
    StrictMonoOn (fun x => f x * c) s :=
  fun _ ha _ hb ab => mul_lt_mul_left (hf ha hb ab) c

@[to_additive add_const]
/-
**StrictAnti.mul_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAnti.mul_const' (hf : StrictAnti f) (c : α) : StrictAnti fun x => f 
x * c
参数：hf : StrictAnti f；c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_left`：mul_lt_mul_left [i : MulRightStrictMono α] {b c : α} (b
c : b < c) (a : α) : b * a < c * a
-/
theorem StrictAnti.mul_const' (hf : StrictAnti f) (c : α) : StrictAnti fun x => f x * c :=
  fun _ _ ab => mul_lt_mul_left (hf ab) c

@[to_additive add_const]
/-
**StrictAntiOn.mul_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAntiOn.mul_const' (hf : StrictAntiOn f s) (c : α) : StrictAntiOn (fu
n x => f x * c) s
参数：hf : StrictAntiOn f s；c : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_left`：mul_lt_mul_left [i : MulRightStrictMono α] {b c : α} (b
c : b < c) (a : α) : b * a < c * a
-/
theorem StrictAntiOn.mul_const' (hf : StrictAntiOn f s) (c : α) :
    StrictAntiOn (fun x => f x * c) s :=
  fun _ ha _ hb ab => mul_lt_mul_left (hf ha hb ab) c

end Right

/-- The product of two strictly monotone functions is strictly monotone. -/
@[to_additive add /-- The sum of two strictly monotone functions is strictly monotone. -/]
/-
**StrictMono.mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.mul' [MulLeftStrictMono α] [MulRightStrictMono α] (hf : StrictM
ono f) (hg : StrictMono g) : StrictMono fun x => f x * g x
参数：hf : StrictMono f；hg : StrictMono g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_of_lt_of_lt`：mul_lt_mul_of_lt_of_lt [MulLeftStrictMono α] [Mu
lRightStrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c < d) : a * c < b * d

--- 原说明 ---
The product of two strictly monotone functions is strictly monotone.
-/
theorem StrictMono.mul' [MulLeftStrictMono α]
    [MulRightStrictMono α] (hf : StrictMono f) (hg : StrictMono g) :
    StrictMono fun x => f x * g x := fun _ _ ab =>
  mul_lt_mul_of_lt_of_lt (hf ab) (hg ab)

/-- The product of two strictly monotone functions is strictly monotone. -/
@[to_additive add /-- The sum of two strictly monotone functions is strictly monotone. -/]
/-
**StrictMonoOn.mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMonoOn.mul' [MulLeftStrictMono α] [MulRightStrictMono α] (hf : Stric
tMonoOn f s) (hg : StrictMonoOn g s) : StrictMonoOn (fun x => f x * g x) s
参数：hf : StrictMonoOn f s；hg : StrictMonoOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_of_lt_of_lt`：mul_lt_mul_of_lt_of_lt [MulLeftStrictMono α] [Mu
lRightStrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c < d) : a * c < b * d

--- 原说明 ---
The product of two strictly monotone functions is strictly monotone.
-/
theorem StrictMonoOn.mul' [MulLeftStrictMono α]
    [MulRightStrictMono α] (hf : StrictMonoOn f s) (hg : StrictMonoOn g s) :
    StrictMonoOn (fun x => f x * g x) s :=
  fun _ ha _ hb ab => mul_lt_mul_of_lt_of_lt (hf ha hb ab) (hg ha hb ab)

/-- The product of two strictly antitone functions is strictly antitone. -/
@[to_additive add /-- The sum of two strictly antitone functions is strictly antitone. -/]
/-
**StrictAnti.mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAnti.mul' [MulLeftStrictMono α] [MulRightStrictMono α] (hf : StrictA
nti f) (hg : StrictAnti g) : StrictAnti fun x => f x * g x
参数：hf : StrictAnti f；hg : StrictAnti g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_of_lt_of_lt`：mul_lt_mul_of_lt_of_lt [MulLeftStrictMono α] [Mu
lRightStrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c < d) : a * c < b * d

--- 原说明 ---
The product of two strictly antitone functions is strictly antitone.
-/
theorem StrictAnti.mul' [MulLeftStrictMono α]
    [MulRightStrictMono α] (hf : StrictAnti f) (hg : StrictAnti g) :
    StrictAnti fun x => f x * g x :=
  fun _ _ ab => mul_lt_mul_of_lt_of_lt (hf ab) (hg ab)

/-- The product of two strictly antitone functions is strictly antitone. -/
@[to_additive add /-- The sum of two strictly antitone functions is strictly antitone. -/]
/-
**StrictAntiOn.mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAntiOn.mul' [MulLeftStrictMono α] [MulRightStrictMono α] (hf : Stric
tAntiOn f s) (hg : StrictAntiOn g s) : StrictAntiOn (fun x => f x * g x) s
参数：hf : StrictAntiOn f s；hg : StrictAntiOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_of_lt_of_lt`：mul_lt_mul_of_lt_of_lt [MulLeftStrictMono α] [Mu
lRightStrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c < d) : a * c < b * d

--- 原说明 ---
The product of two strictly antitone functions is strictly antitone.
-/
theorem StrictAntiOn.mul' [MulLeftStrictMono α]
    [MulRightStrictMono α] (hf : StrictAntiOn f s) (hg : StrictAntiOn g s) :
    StrictAntiOn (fun x => f x * g x) s :=
  fun _ ha _ hb ab => mul_lt_mul_of_lt_of_lt (hf ha hb ab) (hg ha hb ab)

/-- The product of a monotone function and a strictly monotone function is strictly monotone. -/
@[to_additive add_strictMono /-- The sum of a monotone function and a strictly monotone function is
strictly monotone. -/]
/-
**Monotone.mul_strictMono'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.mul_strictMono' [MulLeftStrictMono α] [MulRightMono α] {f g : β -
> α} (hf : Monotone f) (hg : StrictMono g) : StrictMono fun x => f x * g x
参数：hf : Monotone f；hg : StrictMono g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_of_le_of_lt`：mul_lt_mul_of_le_of_lt [MulLeftStrictMono α] [Mu
lRightMono α] {a b c d : α} (h₁ : a <= b) (h₂ : c < d) : a * c < b * d
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem Monotone.mul_strictMono' [MulLeftStrictMono α]
    [MulRightMono α] {f g : β → α} (hf : Monotone f)
    (hg : StrictMono g) :
    StrictMono fun x => f x * g x :=
  fun _ _ h => mul_lt_mul_of_le_of_lt (hf h.le) (hg h)

/-- The product of a monotone function and a strictly monotone function is strictly monotone. -/
@[to_additive add_strictMono /-- The sum of a monotone function and a strictly monotone function is
strictly monotone. -/]
/-
**MonotoneOn.mul_strictMono'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.mul_strictMono' [MulLeftStrictMono α] [MulRightMono α] {f g : β
 -> α} (hf : MonotoneOn f s) (hg : StrictMonoOn g s) : StrictMonoOn (fun x => f 
x * g x) s
参数：hf : MonotoneOn f s；hg : StrictMonoOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_of_le_of_lt`：mul_lt_mul_of_le_of_lt [MulLeftStrictMono α] [Mu
lRightMono α] {a b c d : α} (h₁ : a <= b) (h₂ : c < d) : a * c < b * d
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem MonotoneOn.mul_strictMono' [MulLeftStrictMono α]
    [MulRightMono α] {f g : β → α} (hf : MonotoneOn f s)
    (hg : StrictMonoOn g s) : StrictMonoOn (fun x => f x * g x) s :=
  fun _ hx _ hy h => mul_lt_mul_of_le_of_lt (hf hx hy h.le) (hg hx hy h)

/-- The product of an antitone function and a strictly antitone function is strictly antitone. -/
@[to_additive add_strictAnti /-- The sum of an antitone function and a strictly antitone function is
strictly antitone. -/]
/-
**Antitone.mul_strictAnti'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.mul_strictAnti' [MulLeftStrictMono α] [MulRightMono α] {f g : β -
> α} (hf : Antitone f) (hg : StrictAnti g) : StrictAnti fun x => f x * g x
参数：hf : Antitone f；hg : StrictAnti g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_of_le_of_lt`：mul_lt_mul_of_le_of_lt [MulLeftStrictMono α] [Mu
lRightMono α] {a b c d : α} (h₁ : a <= b) (h₂ : c < d) : a * c < b * d
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem Antitone.mul_strictAnti' [MulLeftStrictMono α]
    [MulRightMono α] {f g : β → α} (hf : Antitone f)
    (hg : StrictAnti g) :
    StrictAnti fun x => f x * g x :=
  fun _ _ h => mul_lt_mul_of_le_of_lt (hf h.le) (hg h)

/-- The product of an antitone function and a strictly antitone function is strictly antitone. -/
@[to_additive add_strictAnti /-- The sum of an antitone function and a strictly antitone function is
strictly antitone. -/]
/-
**AntitoneOn.mul_strictAnti'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.mul_strictAnti' [MulLeftStrictMono α] [MulRightMono α] {f g : β
 -> α} (hf : AntitoneOn f s) (hg : StrictAntiOn g s) : StrictAntiOn (fun x => f 
x * g x) s
参数：hf : AntitoneOn f s；hg : StrictAntiOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_of_le_of_lt`：mul_lt_mul_of_le_of_lt [MulLeftStrictMono α] [Mu
lRightMono α] {a b c d : α} (h₁ : a <= b) (h₂ : c < d) : a * c < b * d
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem AntitoneOn.mul_strictAnti' [MulLeftStrictMono α]
    [MulRightMono α] {f g : β → α} (hf : AntitoneOn f s)
    (hg : StrictAntiOn g s) :
    StrictAntiOn (fun x => f x * g x) s :=
  fun _ hx _ hy h => mul_lt_mul_of_le_of_lt (hf hx hy h.le) (hg hx hy h)

variable [MulLeftMono α] [MulRightStrictMono α]

/-- The product of a strictly monotone function and a monotone function is strictly monotone. -/
@[to_additive add_monotone /-- The sum of a strictly monotone function and a monotone function is
strictly monotone. -/]
/-
**StrictMono.mul_monotone'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.mul_monotone' (hf : StrictMono f) (hg : Monotone g) : StrictMon
o fun x => f x * g x
参数：hf : StrictMono f；hg : Monotone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_of_lt_of_le`：mul_lt_mul_of_lt_of_le [MulLeftMono α] [MulRight
StrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c <= d) : a * c < b * d
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem StrictMono.mul_monotone' (hf : StrictMono f) (hg : Monotone g) :
    StrictMono fun x => f x * g x :=
  fun _ _ h => mul_lt_mul_of_lt_of_le (hf h) (hg h.le)

/-- The product of a strictly monotone function and a monotone function is strictly monotone. -/
@[to_additive add_monotone /-- The sum of a strictly monotone function and a monotone function is
strictly monotone. -/]
/-
**StrictMonoOn.mul_monotone'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMonoOn.mul_monotone' (hf : StrictMonoOn f s) (hg : MonotoneOn g s) :
 StrictMonoOn (fun x => f x * g x) s
参数：hf : StrictMonoOn f s；hg : MonotoneOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_of_lt_of_le`：mul_lt_mul_of_lt_of_le [MulLeftMono α] [MulRight
StrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c <= d) : a * c < b * d
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem StrictMonoOn.mul_monotone' (hf : StrictMonoOn f s) (hg : MonotoneOn g s) :
    StrictMonoOn (fun x => f x * g x) s :=
  fun _ hx _ hy h => mul_lt_mul_of_lt_of_le (hf hx hy h) (hg hx hy h.le)

/-- The product of a strictly antitone function and an antitone function is strictly antitone. -/
@[to_additive add_antitone /-- The sum of a strictly antitone function and an antitone function is
strictly antitone. -/]
/-
**StrictAnti.mul_antitone'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAnti.mul_antitone' (hf : StrictAnti f) (hg : Antitone g) : StrictAnt
i fun x => f x * g x
参数：hf : StrictAnti f；hg : Antitone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_of_lt_of_le`：mul_lt_mul_of_lt_of_le [MulLeftMono α] [MulRight
StrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c <= d) : a * c < b * d
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem StrictAnti.mul_antitone' (hf : StrictAnti f) (hg : Antitone g) :
    StrictAnti fun x => f x * g x :=
  fun _ _ h => mul_lt_mul_of_lt_of_le (hf h) (hg h.le)

/-- The product of a strictly antitone function and an antitone function is strictly antitone. -/
@[to_additive add_antitone /-- The sum of a strictly antitone function and an antitone function is
strictly antitone. -/]
/-
**StrictAntiOn.mul_antitone'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAntiOn.mul_antitone' (hf : StrictAntiOn f s) (hg : AntitoneOn g s) :
 StrictAntiOn (fun x => f x * g x) s
参数：hf : StrictAntiOn f s；hg : AntitoneOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_of_lt_of_le`：mul_lt_mul_of_lt_of_le [MulLeftMono α] [MulRight
StrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c <= d) : a * c < b * d
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem StrictAntiOn.mul_antitone' (hf : StrictAntiOn f s) (hg : AntitoneOn g s) :
    StrictAntiOn (fun x => f x * g x) s :=
  fun _ hx _ hy h => mul_lt_mul_of_lt_of_le (hf hx hy h) (hg hx hy h.le)

@[to_additive (attr := simp) cmp_add_left]
/-
**cmp_mul_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cmp_mul_left' {α : Type*} [Mul α] [LinearOrder α] [MulLeftStrictMono α] (a
 b c : α) : cmp (a * b) (a * c) = cmp b c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.cmp_map_eq`：StrictMono.cmp_map_eq (hf : StrictMono f) (x y : 
α) : cmp (f x) (f y) = cmp x y
· 使用定理 `StrictMono.const_mul'`：StrictMono.const_mul' (hf : StrictMono f) (c : α)
 : StrictMono fun x => c * f x
· 使用定理 `strictMono_id`：strictMono_id [Preorder α] : StrictMono (id : α -> α)
-/
theorem cmp_mul_left' {α : Type*} [Mul α] [LinearOrder α] [MulLeftStrictMono α]
    (a b c : α) :
    cmp (a * b) (a * c) = cmp b c :=
  (strictMono_id.const_mul' a).cmp_map_eq b c

@[to_additive (attr := simp) cmp_add_right]
/-
**cmp_mul_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cmp_mul_right' {α : Type*} [Mul α] [LinearOrder α] [MulRightStrictMono α] 
(a b c : α) : cmp (a * c) (b * c) = cmp a b
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.cmp_map_eq`：StrictMono.cmp_map_eq (hf : StrictMono f) (x y : 
α) : cmp (f x) (f y) = cmp x y
· 使用定理 `StrictMono.mul_const'`：StrictMono.mul_const' (hf : StrictMono f) (c : α)
 : StrictMono fun x => f x * c
· 使用定理 `strictMono_id`：strictMono_id [Preorder α] : StrictMono (id : α -> α)
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
/-
**MulLECancellable** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulLECancellable [Mul α] [LE α] (a : α) : Prop
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MulLECancellable [Mul α] [LE α] (a : α) : Prop :=
  ∀ ⦃b c⦄, a * b ≤ a * c → b ≤ c

@[to_additive]
/-
**Contravariant.MulLECancellable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Contravariant.MulLECancellable [Mul α] [LE α] [MulLeftReflectLE α] {a : α}
 : MulLECancellable a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_mul_le_mul_left'`：le_of_mul_le_mul_left' [MulLeftReflectLE α] {a b
 c : α} (bc : a * b <= a * c) : b <= c
-/
theorem Contravariant.MulLECancellable [Mul α] [LE α] [MulLeftReflectLE α]
    {a : α} :
    MulLECancellable a :=
  fun _ _ => le_of_mul_le_mul_left'

@[to_additive (attr := simp)]
/-
**mulLECancellable_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulLECancellable_one [MulOneClass α] [LE α] : MulLECancellable (1 : α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem mulLECancellable_one [MulOneClass α] [LE α] : MulLECancellable (1 : α) := fun a b => by
  simpa only [one_mul] using id

namespace MulLECancellable

@[to_additive]
/-
**MulLECancellable.Injective** 是 Mathlib 中的一个定理，位于命名空间 `MulLECancellable`。
形式化陈述：∀ {α : Type u_1} [inst : Mul α] [inst_1 : PartialOrder α] {a : α},   MulLE
Cancellable a → Function.Injective fun x => a * x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
protected theorem Injective [Mul α] [PartialOrder α] {a : α} (ha : MulLECancellable a) :
    Injective (a * ·) :=
  fun _ _ h => le_antisymm (ha h.le) (ha h.ge)

@[to_additive]
/-
**MulLECancellable.isLeftRegular** 是 Mathlib 中的一个定理，位于命名空间 `MulLECancellable`。
形式化陈述：∀ {α : Type u_1} [inst : Mul α] [inst_1 : PartialOrder α] {a : α}, MulLECa
ncellable a → IsLeftRegular a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulLECancellable.Injective`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Pa
rtialOrder α] {a : α},   MulLECancellable a → Function.Injective fun x => a * x
-/
protected theorem isLeftRegular [Mul α] [PartialOrder α] {a : α}
    (ha : MulLECancellable a) : IsLeftRegular a :=
  ha.Injective

@[to_additive]
/-
**MulLECancellable.inj** 是 Mathlib 中的一个定理，位于命名空间 `MulLECancellable`。
形式化陈述：∀ {α : Type u_1} [inst : Mul α] [inst_1 : PartialOrder α] {a b c : α}, Mul
LECancellable a → (a * b = a * c ↔ b = c)
参数：a * b = a * c ↔ b = c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `MulLECancellable.Injective`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Pa
rtialOrder α] {a : α},   MulLECancellable a → Function.Injective fun x => a * x
-/
protected theorem inj [Mul α] [PartialOrder α] {a b c : α} (ha : MulLECancellable a) :
    a * b = a * c ↔ b = c :=
  ha.Injective.eq_iff

@[to_additive]
/-
**MulLECancellable.injective_left** 是 Mathlib 中的一个定理，位于命名空间 `MulLECancellable`。
形式化陈述：∀ {α : Type u_1} [inst : Mul α] [IsMulCommutative α] [inst_2 : PartialOrde
r α] {a : α},   MulLECancellable a → Function.Injective fun x => x * a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulLECancellable.Injective`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Pa
rtialOrder α] {a : α},   MulLECancellable a → Function.Injective fun x => a * x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_comm'`：mul_comm' {M : Type*} [Mul M] [IsMulCommutative M] (a b : M) 
: a * b = b * a
-/
protected theorem injective_left [Mul α] [IsMulCommutative α] [PartialOrder α] {a : α}
    (ha : MulLECancellable a) : Injective (· * a) :=
  fun b c h ↦ ha.Injective <| by dsimp; rwa [mul_comm' a, mul_comm' a]

@[to_additive]
/-
**MulLECancellable.inj_left** 是 Mathlib 中的一个定理，位于命名空间 `MulLECancellable`。
形式化陈述：∀ {α : Type u_1} [inst : Mul α] [IsMulCommutative α] [inst_2 : PartialOrde
r α] {a b c : α},   MulLECancellable c → (a * c = b * c ↔ a = b)
参数：a * c = b * c ↔ a = b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `MulLECancellable.injective_left`：∀ {α : Type u_1} [inst : Mul α] [IsMulC
ommutative α] [inst_2 : PartialOrder α] {a : α},   MulLECancellable a → Function
.Injective fun x => x…
-/
protected theorem inj_left [Mul α] [IsMulCommutative α] [PartialOrder α] {a b c : α}
    (hc : MulLECancellable c) : a * c = b * c ↔ a = b :=
  hc.injective_left.eq_iff

variable [LE α]

@[to_additive]
/-
**MulLECancellable.mul_le_mul_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `MulLECancellab
le`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] [inst_1 : Mul α] [MulLeftMono α] {a b c : α
},   MulLECancellable a → (a * b ≤ a * c ↔ b ≤ c)
参数：a * b ≤ a * c ↔ b ≤ c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
-/
protected theorem mul_le_mul_iff_left [Mul α] [MulLeftMono α] {a b c : α}
    (ha : MulLECancellable a) : a * b ≤ a * c ↔ b ≤ c :=
  ⟨fun h => ha h, fun h => mul_le_mul_right h a⟩

@[to_additive]
/-
**MulLECancellable.mul_le_mul_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `MulLECancella
ble`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] [inst_1 : Mul α] [IsMulCommutative α] [MulL
eftMono α] {a b c : α},   MulLECancellable a → (b * a ≤ c * a ↔ b ≤ c)
参数：b * a ≤ c * a ↔ b ≤ c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_comm'`：mul_comm' {M : Type*} [Mul M] [IsMulCommutative M] (a b : M) 
: a * b = b * a
· 使用定理 `MulLECancellable.mul_le_mul_iff_left`：∀ {α : Type u_1} [inst : LE α] [in
st_1 : Mul α] [MulLeftMono α] {a b c : α},   MulLECancellable a → (a * b ≤ a * c
 ↔ b ≤ c)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem mul_le_mul_iff_right [Mul α] [IsMulCommutative α] [MulLeftMono α] {a b c : α}
    (ha : MulLECancellable a) : b * a ≤ c * a ↔ b ≤ c := by
  rw [mul_comm' b, mul_comm' c, ha.mul_le_mul_iff_left]

@[to_additive]
/-
**MulLECancellable.le_mul_iff_one_le_right** 是 Mathlib 中的一个定理，位于命名空间 `MulLECance
llable`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] [inst_1 : MulOneClass α] [MulLeftMono α] {a
 b : α},   MulLECancellable a → (a ≤ a * b ↔ 1 ≤ b)
参数：a ≤ a * b ↔ 1 ≤ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `MulLECancellable.mul_le_mul_iff_left`：∀ {α : Type u_1} [inst : LE α] [in
st_1 : Mul α] [MulLeftMono α] {a b c : α},   MulLECancellable a → (a * b ≤ a * c
 ↔ b ≤ c)
-/
protected theorem le_mul_iff_one_le_right [MulOneClass α] [MulLeftMono α]
    {a b : α} (ha : MulLECancellable a) :
    a ≤ a * b ↔ 1 ≤ b :=
  Iff.trans (by rw [mul_one]) ha.mul_le_mul_iff_left

@[to_additive]
/-
**MulLECancellable.mul_le_iff_le_one_right** 是 Mathlib 中的一个定理，位于命名空间 `MulLECance
llable`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] [inst_1 : MulOneClass α] [MulLeftMono α] {a
 b : α},   MulLECancellable a → (a * b ≤ a ↔ b ≤ 1)
参数：a * b ≤ a ↔ b ≤ 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `MulLECancellable.mul_le_mul_iff_left`：∀ {α : Type u_1} [inst : LE α] [in
st_1 : Mul α] [MulLeftMono α] {a b c : α},   MulLECancellable a → (a * b ≤ a * c
 ↔ b ≤ c)
-/
protected theorem mul_le_iff_le_one_right [MulOneClass α] [MulLeftMono α]
    {a b : α} (ha : MulLECancellable a) :
    a * b ≤ a ↔ b ≤ 1 :=
  Iff.trans (by rw [mul_one]) ha.mul_le_mul_iff_left

@[to_additive]
/-
**MulLECancellable.le_mul_iff_one_le_left** 是 Mathlib 中的一个定理，位于命名空间 `MulLECancel
lable`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] [inst_1 : MulOneClass α] [IsMulCommutative 
α] [MulLeftMono α] {a b : α},   MulLECancellable a → (a ≤ b * a ↔ 1 ≤ b)
参数：a ≤ b * a ↔ 1 ≤ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_comm'`：mul_comm' {M : Type*} [Mul M] [IsMulCommutative M] (a b : M) 
: a * b = b * a
· 使用定理 `MulLECancellable.le_mul_iff_one_le_right`：∀ {α : Type u_1} [inst : LE α]
 [inst_1 : MulOneClass α] [MulLeftMono α] {a b : α},   MulLECancellable a → (a ≤
 a * b ↔ 1 ≤ b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem le_mul_iff_one_le_left [MulOneClass α] [IsMulCommutative α] [MulLeftMono α]
    {a b : α} (ha : MulLECancellable a) : a ≤ b * a ↔ 1 ≤ b := by
  rw [mul_comm', ha.le_mul_iff_one_le_right]

@[to_additive]
/-
**MulLECancellable.mul_le_iff_le_one_left** 是 Mathlib 中的一个定理，位于命名空间 `MulLECancel
lable`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] [inst_1 : MulOneClass α] [IsMulCommutative 
α] [MulLeftMono α] {a b : α},   MulLECancellable a → (b * a ≤ a ↔ b ≤ 1)
参数：b * a ≤ a ↔ b ≤ 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_comm'`：mul_comm' {M : Type*} [Mul M] [IsMulCommutative M] (a b : M) 
: a * b = b * a
· 使用定理 `MulLECancellable.mul_le_iff_le_one_right`：∀ {α : Type u_1} [inst : LE α]
 [inst_1 : MulOneClass α] [MulLeftMono α] {a b : α},   MulLECancellable a → (a *
 b ≤ a ↔ b ≤ 1)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem mul_le_iff_le_one_left [MulOneClass α] [IsMulCommutative α] [MulLeftMono α]
    {a b : α} (ha : MulLECancellable a) : b * a ≤ a ↔ b ≤ 1 := by
  rw [mul_comm', ha.mul_le_iff_le_one_right]
/-
**MulLECancellable.mul** 是 Mathlib 中的一个定理，位于命名空间 `MulLECancellable`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] [inst_1 : Semigroup α] {a b : α},   MulLECa
ncellable a → MulLECancellable b → MulLECancellable (a * b)
参数：a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
@[to_additive] lemma mul [Semigroup α] {a b : α} (ha : MulLECancellable a)
    (hb : MulLECancellable b) : MulLECancellable (a * b) :=
  fun c d hcd ↦ hb <| ha <| by rwa [← mul_assoc, ← mul_assoc]
/-
**MulLECancellable.of_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `MulLECancellable`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] [inst_1 : Semigroup α] [MulLeftMono α] {a b
 : α},   MulLECancellable (a * b) → MulLECancellable b
参数：a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
-/
@[to_additive] lemma of_mul_right [Semigroup α] [MulLeftMono α] {a b : α}
    (h : MulLECancellable (a * b)) : MulLECancellable b :=
  fun c d hcd ↦ h <| by rw [mul_assoc, mul_assoc]; exact mul_le_mul_right hcd _
/-
**MulLECancellable.of_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `MulLECancellable`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] [inst_1 : CommSemigroup α] [MulLeftMono α] 
{a b : α},   MulLECancellable (a * b) → MulLECancellable a
参数：a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulLECancellable.of_mul_right`：∀ {α : Type u_1} [inst : LE α] [inst_1 : 
Semigroup α] [MulLeftMono α] {a b : α},   MulLECancellable (a * b) → MulLECancel
lable b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
@[to_additive] lemma of_mul_left [CommSemigroup α] [MulLeftMono α] {a b : α}
    (h : MulLECancellable (a * b)) : MulLECancellable a := (mul_comm a b ▸ h).of_mul_right

end MulLECancellable

@[to_additive (attr := simp)]
/-
**mulLECancellable_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mulLECancellable_mul [LE α] [CommSemigroup α] [MulLeftMono α] {a b : α} : 
MulLECancellable (a * b) ↔ MulLECancellable a ∧ MulLECancellable b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulLECancellable.of_mul_left`：∀ {α : Type u_1} [inst : LE α] [inst_1 : C
ommSemigroup α] [MulLeftMono α] {a b : α},   MulLECancellable (a * b) → MulLECan
cellable a
· 使用定理 `MulLECancellable.of_mul_right`：∀ {α : Type u_1} [inst : LE α] [inst_1 : 
Semigroup α] [MulLeftMono α] {a b : α},   MulLECancellable (a * b) → MulLECancel
lable b
· 使用定理 `MulLECancellable.mul`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Semigroup
 α] {a b : α},   MulLECancellable a → MulLECancellable b → MulLECancellable (a *
 b)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma mulLECancellable_mul [LE α] [CommSemigroup α] [MulLeftMono α] {a b : α} :
    MulLECancellable (a * b) ↔ MulLECancellable a ∧ MulLECancellable b :=
  ⟨fun h ↦ ⟨h.of_mul_left, h.of_mul_right⟩, fun h ↦ h.1.mul h.2⟩
