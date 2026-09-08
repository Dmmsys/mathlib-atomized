/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Data.ENNReal.Real
public import Mathlib.Tactic.Finiteness

/-!
# Properties of addition, multiplication and subtraction on extended non-negative real numbers

In this file we prove elementary properties of algebraic operations on `ℝ≥0∞`, including addition,
multiplication, natural powers and truncated subtraction, as well as how these interact with the
order structure on `ℝ≥0∞`. Notably excluded from this list are inversion and division, the
definitions and properties of which can be found in `Mathlib/Data/ENNReal/Inv.lean`.

Note: the definitions of the operations included in this file can be found in
`Mathlib/Data/ENNReal/Basic.lean`.
-/

public section

assert_not_exists Finset

open Set NNReal ENNReal

namespace ENNReal

variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

section Mul

@[mono, gcongr]
/-
**ENNReal.mul_lt_mul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：mul_lt_mul (ac : a < c) (bd : b < d) : a * b < c * d
参数：ac : a < c；bd : b < d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.mul_lt_mul`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Co
mmSemiring α] [inst_2 : PartialOrder α] [OrderBot α]   [inst_4 : CanonicallyOrde
redAdd α…
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
-/
theorem mul_lt_mul (ac : a < c) (bd : b < d) : a * b < c * d := WithTop.mul_lt_mul ac bd
/-
**ENNReal.pow_right_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {n : ℕ}, n ≠ 0 → StrictMono fun a => a ^ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.pow_right_strictMono`：∀ {α : Type u_1} [inst : DecidableEq α] [i
nst_1 : CommSemiring α] [inst_2 : PartialOrder α] [OrderBot α]   [inst_4 : Canon
icallyOrderedAdd α…
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `NNReal.instNoZeroDivisors`：NoZeroDivisors NNReal
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
-/
protected lemma pow_right_strictMono {n : ℕ} (hn : n ≠ 0) : StrictMono fun a : ℝ≥0∞ ↦ a ^ n :=
  WithTop.pow_right_strictMono hn
/-
**ENNReal.pow_le_pow_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal} {n : ℕ}, n ≠ 0 → (a ^ n ≤ b ^ n ↔ a ≤ b)
参数：a ^ n ≤ b ^ n ↔ a ≤ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `ENNReal.pow_right_strictMono`：∀ {n : ℕ}, n ≠ 0 → StrictMono fun a => a ^
 n
-/
protected lemma pow_le_pow_left_iff {n : ℕ} (hn : n ≠ 0) : a ^ n ≤ b ^ n ↔ a ≤ b :=
  (ENNReal.pow_right_strictMono hn).le_iff_le
/-
**ENNReal.pow_lt_pow_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal} {n : ℕ}, n ≠ 0 → (a ^ n < b ^ n ↔ a < b)
参数：a ^ n < b ^ n ↔ a < b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `ENNReal.pow_right_strictMono`：∀ {n : ℕ}, n ≠ 0 → StrictMono fun a => a ^
 n
-/
protected lemma pow_lt_pow_left_iff {n : ℕ} (hn : n ≠ 0) : a ^ n < b ^ n ↔ a < b :=
  (ENNReal.pow_right_strictMono hn).lt_iff_lt
/-
**ENNReal.pow_le_pow_left** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal} {n : ℕ}, a ≤ b → a ^ n ≤ b ^ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_le_pow_left'`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preorder 
M] [MulLeftMono M] [MulRightMono M] {a b : M},   a ≤ b → ∀ (i : ℕ), a ^ i ≤ b ^ 
i
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
-/
@[mono, gcongr] protected lemma pow_le_pow_left {n : ℕ} (h : a ≤ b) : a ^ n ≤ b ^ n :=
  pow_le_pow_left' h n
@[mono, gcongr] protected alias ⟨_, pow_lt_pow_left⟩ := ENNReal.pow_lt_pow_left_iff
/-
**ENNReal.mul_left_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：mul_left_strictMono (h₀ : a != 0) (hinf : a != ∞) : StrictMono (· * a)
参数：h₀ : a != 0；hinf : a != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.mul_left_strictMono`：∀ {α : Type u_1} [inst : DecidableEq α] [in
st_1 : MulZeroClass α] {a : WithTop α} [inst_2 : Preorder α]   [MulPosStrictMono
 α], 0 < a → a ≠ …
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `WithTop.instIsBotZeroClass`：∀ {α : Type u} [inst : Zero α] [inst_1 : LE 
α] [IsBotZeroClass α], IsBotZeroClass (WithTop α)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
lemma mul_left_strictMono (h₀ : a ≠ 0) (hinf : a ≠ ∞) : StrictMono (· * a) :=
  WithTop.mul_left_strictMono (pos_iff_ne_zero.2 h₀) hinf
/-
**ENNReal.mul_right_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：mul_right_strictMono (h₀ : a != 0) (hinf : a != ∞) : StrictMono (a * ·)
参数：h₀ : a != 0；hinf : a != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.mul_right_strictMono`：∀ {α : Type u_1} [inst : DecidableEq α] [i
nst_1 : MulZeroClass α] {a : WithTop α} [inst_2 : Preorder α]   [PosMulStrictMon
o α], 0 < a → a ≠ …
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `WithTop.instIsBotZeroClass`：∀ {α : Type u} [inst : Zero α] [inst_1 : LE 
α] [IsBotZeroClass α], IsBotZeroClass (WithTop α)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
lemma mul_right_strictMono (h₀ : a ≠ 0) (hinf : a ≠ ∞) : StrictMono (a * ·) :=
  WithTop.mul_right_strictMono (pos_iff_ne_zero.2 h₀) hinf
/-
**ENNReal.mul_lt_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, a ≠ 0 → a ≠ ⊤ → b < c → a * b < a * c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.mul_right_strictMono`：mul_right_strictMono (h₀ : a != 0) (hinf :
 a != ∞) : StrictMono (a * ·)
-/
@[gcongr] protected theorem mul_lt_mul_right (h0 : a ≠ 0) (hinf : a ≠ ⊤) (bc : b < c) :
    a * b < a * c :=
  ENNReal.mul_right_strictMono h0 hinf bc
/-
**ENNReal.mul_lt_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, a ≠ 0 → a ≠ ⊤ → b < c → b * a < c * a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.mul_right_strictMono`：mul_right_strictMono (h₀ : a != 0) (hinf :
 a != ∞) : StrictMono (a * ·)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
@[gcongr] protected theorem mul_lt_mul_left (h0 : a ≠ 0) (hinf : a ≠ ⊤) (bc : b < c) :
    b * a < c * a :=
  mul_comm b a ▸ mul_comm c a ▸ ENNReal.mul_right_strictMono h0 hinf bc

-- TODO: generalize to `WithTop`
/-
**ENNReal.mul_right_inj** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, a ≠ 0 → a ≠ ⊤ → (a * b = a * c ↔ b = c)
参数：a * b = a * c ↔ b = c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用引理 `ENNReal.mul_right_strictMono`：mul_right_strictMono (h₀ : a != 0) (hinf :
 a != ∞) : StrictMono (a * ·)
-/
protected theorem mul_right_inj (h0 : a ≠ 0) (hinf : a ≠ ∞) : a * b = a * c ↔ b = c :=
  (mul_right_strictMono h0 hinf).injective.eq_iff

-- TODO: generalize to `WithTop`
/-
**ENNReal.mul_left_inj** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, c ≠ 0 → c ≠ ⊤ → (a * c = b * c ↔ a = b)
参数：a * c = b * c ↔ a = b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.mul_right_inj`：∀ {a b c : ENNReal}, a ≠ 0 → a ≠ ⊤ → (a * b = a *
 c ↔ b = c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
protected theorem mul_left_inj (h0 : c ≠ 0) (hinf : c ≠ ∞) : a * c = b * c ↔ a = b :=
  mul_comm c a ▸ mul_comm c b ▸ ENNReal.mul_right_inj h0 hinf

-- TODO: generalize to `WithTop`
/-
**ENNReal.mul_le_mul_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, a ≠ 0 → a ≠ ⊤ → (a * b ≤ a * c ↔ b ≤ c)
参数：a * b ≤ a * c ↔ b ≤ c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用引理 `ENNReal.mul_right_strictMono`：mul_right_strictMono (h₀ : a != 0) (hinf :
 a != ∞) : StrictMono (a * ·)
-/
protected lemma mul_le_mul_iff_right (h0 : a ≠ 0) (hinf : a ≠ ∞) : a * b ≤ a * c ↔ b ≤ c :=
  (mul_right_strictMono h0 hinf).le_iff_le

-- TODO: generalize to `WithTop`
/-
**ENNReal.mul_le_mul_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, c ≠ 0 → c ≠ ⊤ → (a * c ≤ b * c ↔ a ≤ b)
参数：a * c ≤ b * c ↔ a ≤ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用引理 `ENNReal.mul_left_strictMono`：mul_left_strictMono (h₀ : a != 0) (hinf : a
 != ∞) : StrictMono (· * a)
-/
protected lemma mul_le_mul_iff_left (h0 : c ≠ 0) (hinf : c ≠ ∞) : a * c ≤ b * c ↔ a ≤ b :=
  (mul_left_strictMono h0 hinf).le_iff_le

-- TODO: generalize to `WithTop`
/-
**ENNReal.mul_lt_mul_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, a ≠ 0 → a ≠ ⊤ → (a * b < a * c ↔ b < c)
参数：a * b < a * c ↔ b < c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用引理 `ENNReal.mul_right_strictMono`：mul_right_strictMono (h₀ : a != 0) (hinf :
 a != ∞) : StrictMono (a * ·)
-/
protected lemma mul_lt_mul_iff_right (h0 : a ≠ 0) (hinf : a ≠ ∞) : a * b < a * c ↔ b < c :=
  (mul_right_strictMono h0 hinf).lt_iff_lt

-- TODO: generalize to `WithTop`
/-
**ENNReal.mul_lt_mul_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, c ≠ 0 → c ≠ ⊤ → (a * c < b * c ↔ a < b)
参数：a * c < b * c ↔ a < b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用引理 `ENNReal.mul_left_strictMono`：mul_left_strictMono (h₀ : a != 0) (hinf : a
 != ∞) : StrictMono (· * a)
-/
protected lemma mul_lt_mul_iff_left (h0 : c ≠ 0) (hinf : c ≠ ∞) : a * c < b * c ↔ a < b :=
  (mul_left_strictMono h0 hinf).lt_iff_lt
/-
**ENNReal.mul_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, a ≠ 0 → a ≠ ⊤ → (a * b = a ↔ b = 1)
参数：a * b = a ↔ b = 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ENNReal.mul_right_inj`：∀ {a b c : ENNReal}, a ≠ 0 → a ≠ ⊤ → (a * b = a *
 c ↔ b = c)
-/
protected lemma mul_eq_left (ha₀ : a ≠ 0) (ha : a ≠ ∞) : a * b = a ↔ b = 1 := by
  simpa using ENNReal.mul_right_inj ha₀ ha (c := 1)
/-
**ENNReal.mul_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, b ≠ 0 → b ≠ ⊤ → (a * b = b ↔ a = 1)
参数：a * b = b ↔ a = 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `ENNReal.mul_left_inj`：∀ {a b c : ENNReal}, c ≠ 0 → c ≠ ⊤ → (a * c = b * 
c ↔ a = b)
-/
protected lemma mul_eq_right (hb₀ : b ≠ 0) (hb : b ≠ ∞) : a * b = b ↔ a = 1 := by
  simpa using ENNReal.mul_left_inj hb₀ hb (b := 1)

end Mul

section OperationsAndOrder

/-
**ENNReal.pow_pos** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal}, 0 < a → ∀ (n : ℕ), 0 < a ^ n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CanonicallyOrderedAdd.pow_pos`：pow_pos [IsReduced R] {a : R} (ha : 0 < a
) (n : Nat) : 0 < a ^ n
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
-/
protected theorem pow_pos : 0 < a → ∀ n : ℕ, 0 < a ^ n :=
  CanonicallyOrderedAdd.pow_pos
/-
**ENNReal.pow_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal}, a ≠ 0 → ∀ (n : ℕ), a ^ n ≠ 0
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `ENNReal.pow_pos`：∀ {a : ENNReal}, 0 < a → ∀ (n : ℕ), 0 < a ^ n
-/
protected theorem pow_ne_zero : a ≠ 0 → ∀ n : ℕ, a ^ n ≠ 0 := by
  simpa only [pos_iff_ne_zero] using ENNReal.pow_pos
/-
**ENNReal.not_lt_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：not_lt_zero : ¬a < 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem not_lt_zero : ¬a < 0 := by simp
/-
**ENNReal.le_of_add_le_add_left** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, a ≠ ⊤ → a + b ≤ a + c → b ≤ c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.le_of_add_le_add_left`：∀ {α : Type u} [inst : Add α] {x y z : Wi
thTop α} [inst_1 : LE α] [AddLeftReflectLE α], x ≠ ⊤ → x + y ≤ x + z → y ≤ z
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
-/
protected theorem le_of_add_le_add_left : a ≠ ∞ → a + b ≤ a + c → b ≤ c :=
  WithTop.le_of_add_le_add_left
/-
**ENNReal.le_of_add_le_add_right** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, a ≠ ⊤ → b + a ≤ c + a → b ≤ c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.le_of_add_le_add_right`：∀ {α : Type u} [inst : Add α] {x y z : W
ithTop α} [inst_1 : LE α] [AddRightReflectLE α], z ≠ ⊤ → x + z ≤ y + z → x ≤ y
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
-/
protected theorem le_of_add_le_add_right : a ≠ ∞ → b + a ≤ c + a → b ≤ c :=
  WithTop.le_of_add_le_add_right
/-
**ENNReal.add_lt_add_left** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, a ≠ ⊤ → b < c → a + b < a + c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.add_lt_add_left`：∀ {α : Type u} [inst : Add α] {x y z : WithTop 
α} [inst_1 : LT α] [AddLeftStrictMono α], x ≠ ⊤ → y < z → x + y < x + z
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
-/
@[gcongr] protected theorem add_lt_add_left : a ≠ ∞ → b < c → a + b < a + c :=
  WithTop.add_lt_add_left
/-
**ENNReal.add_lt_add_right** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, a ≠ ⊤ → b < c → b + a < c + a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.add_lt_add_right`：∀ {α : Type u} [inst : Add α] {x y z : WithTop
 α} [inst_1 : LT α] [AddRightStrictMono α], z ≠ ⊤ → x < y → x + z < y + z
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
@[gcongr] protected theorem add_lt_add_right : a ≠ ∞ → b < c → b + a < c + a :=
  WithTop.add_lt_add_right
/-
**ENNReal.add_le_add_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, a ≠ ⊤ → (a + b ≤ a + c ↔ b ≤ c)
参数：a + b ≤ a + c ↔ b ≤ c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.add_le_add_iff_left`：∀ {α : Type u} [inst : Add α] {x y z : With
Top α} [inst_1 : LE α] [AddLeftMono α] [AddLeftReflectLE α],   x ≠ ⊤ → (x + y ≤ 
x + z ↔ y ≤ z)
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
-/
protected theorem add_le_add_iff_left : a ≠ ∞ → (a + b ≤ a + c ↔ b ≤ c) :=
  WithTop.add_le_add_iff_left
/-
**ENNReal.add_le_add_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, a ≠ ⊤ → (b + a ≤ c + a ↔ b ≤ c)
参数：b + a ≤ c + a ↔ b ≤ c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.add_le_add_iff_right`：∀ {α : Type u} [inst : Add α] {x y z : Wit
hTop α} [inst_1 : LE α] [AddRightMono α] [AddRightReflectLE α],   z ≠ ⊤ → (x + z
 ≤ y + z ↔ x ≤ y)
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
-/
protected theorem add_le_add_iff_right : a ≠ ∞ → (b + a ≤ c + a ↔ b ≤ c) :=
  WithTop.add_le_add_iff_right
/-
**ENNReal.add_lt_add_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, a ≠ ⊤ → (a + b < a + c ↔ b < c)
参数：a + b < a + c ↔ b < c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.add_lt_add_iff_left`：∀ {α : Type u} [inst : Add α] {x y z : With
Top α} [inst_1 : LT α] [AddLeftStrictMono α] [AddLeftReflectLT α],   x ≠ ⊤ → (x 
+ y < x + z ↔ y <…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
-/
protected theorem add_lt_add_iff_left : a ≠ ∞ → (a + b < a + c ↔ b < c) :=
  WithTop.add_lt_add_iff_left
/-
**ENNReal.add_lt_add_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, a ≠ ⊤ → (b + a < c + a ↔ b < c)
参数：b + a < c + a ↔ b < c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.add_lt_add_iff_right`：∀ {α : Type u} [inst : Add α] {x y z : Wit
hTop α} [inst_1 : LT α] [AddRightStrictMono α] [AddRightReflectLT α],   z ≠ ⊤ → 
(x + z < y + z ↔ x…
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
-/
protected theorem add_lt_add_iff_right : a ≠ ∞ → (b + a < c + a ↔ b < c) :=
  WithTop.add_lt_add_iff_right
/-
**ENNReal.add_lt_add_of_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c d : ENNReal}, a ≠ ⊤ → a ≤ b → c < d → a + c < b + d
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.add_lt_add_of_le_of_lt`：∀ {α : Type u} [inst : Add α] {w x y z :
 WithTop α} [inst_1 : Preorder α] [AddLeftStrictMono α] [AddRightMono α],   w ≠ 
⊤ → w ≤ y → x < z → …
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
protected theorem add_lt_add_of_le_of_lt : a ≠ ∞ → a ≤ b → c < d → a + c < b + d :=
  WithTop.add_lt_add_of_le_of_lt
/-
**ENNReal.add_lt_add_of_lt_of_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c d : ENNReal}, c ≠ ⊤ → a < b → c ≤ d → a + c < b + d
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.add_lt_add_of_lt_of_le`：∀ {α : Type u} [inst : Add α] {w x y z :
 WithTop α} [inst_1 : Preorder α] [AddLeftMono α] [AddRightStrictMono α],   x ≠ 
⊤ → w < y → x ≤ z → …
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
protected theorem add_lt_add_of_lt_of_le : c ≠ ∞ → a < b → c ≤ d → a + c < b + d :=
  WithTop.add_lt_add_of_lt_of_le
/-
**ENNReal.addLeftReflectLT** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
形式化陈述：addLeftReflectLT : AddLeftReflectLT Real>=0∞
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addLeftReflectLT : AddLeftReflectLT ℝ≥0∞ :=
  WithTop.addLeftReflectLT
/-
**ENNReal.lt_add_right** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：lt_add_right (ha : a != ∞) (hb : b != 0) : a < a + b
参数：ha : a != ∞；hb : b != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.add_lt_add_iff_left`：∀ {a b c : ENNReal}, a ≠ ⊤ → (a + b < a + c
 ↔ b < c)
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
theorem lt_add_right (ha : a ≠ ∞) (hb : b ≠ 0) : a < a + b := by
  rwa [← pos_iff_ne_zero, ← ENNReal.add_lt_add_iff_left ha, add_zero] at hb

end OperationsAndOrder

section OperationsAndInfty

variable {α : Type*} {n : ℕ}

/-
**ENNReal.add_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.add_eq_top`：∀ {α : Type u} [inst : Add α] {x y : WithTop α}, x +
 y = ⊤ ↔ x = ⊤ ∨ y = ⊤
-/
@[simp] theorem add_eq_top : a + b = ∞ ↔ a = ∞ ∨ b = ∞ := WithTop.add_eq_top
/-
**ENNReal.add_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.add_lt_top`：add_lt_top [LT α] : x + y < ⊤ ↔ x < ⊤ ∧ y < ⊤
-/
@[simp] theorem add_lt_top : a + b < ∞ ↔ a < ∞ ∧ b < ∞ := WithTop.add_lt_top
/-
**ENNReal.toNNReal_add** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toNNReal_add {r₁ r₂ : Real>=0∞} (h₁ : r₁ != ∞) (h₂ : r₂ != ∞) : (r₁ + r₂).
toNNReal = r₁.toNNReal + r₂.toNNReal
参数：h₁ : r₁ != ∞；h₂ : r₂ != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
-/
theorem toNNReal_add {r₁ r₂ : ℝ≥0∞} (h₁ : r₁ ≠ ∞) (h₂ : r₂ ≠ ∞) :
    (r₁ + r₂).toNNReal = r₁.toNNReal + r₂.toNNReal := by
  lift r₁ to ℝ≥0 using h₁
  lift r₂ to ℝ≥0 using h₂
  rfl

/-- If `a ≤ b + c` and `a = ∞` whenever `b = ∞` or `c = ∞`, then
`ENNReal.toReal a ≤ ENNReal.toReal b + ENNReal.toReal c`. This lemma is useful to transfer
triangle-like inequalities from `ENNReal`s to `Real`s. -/
/-
**ENNReal.toReal_le_add'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_le_add' (hle : a <= b + c) (hb : b = ∞ -> a = ∞) (hc : c = ∞ -> a =
 ∞) : a.toReal <= b.toReal + c.toReal
参数：hle : a <= b + c；hb : b = ∞ -> a = ∞；hc : c = ∞ -> a = ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `ENNReal.toReal_mono'`：toReal_mono' (h : a <= b) (ht : b = ∞ -> a = ∞) : 
a.toReal <= b.toReal
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ENNReal.toReal_add_le`：toReal_add_le : (a + b).toReal <= a.toReal + b.to
Real

--- 原说明 ---
If `a ≤ b + c` and `a = ∞` whenever `b = ∞` or `c = ∞`, then
`ENNReal.toReal a ≤ ENNReal.toReal b + ENNReal.toReal c`. This lemma is useful t
o transfer
triangle-like inequalities from `ENNReal`s to `Real`s.
-/
theorem toReal_le_add' (hle : a ≤ b + c) (hb : b = ∞ → a = ∞) (hc : c = ∞ → a = ∞) :
    a.toReal ≤ b.toReal + c.toReal := by
  refine le_trans (toReal_mono' hle ?_) toReal_add_le
  simpa only [add_eq_top, or_imp] using And.intro hb hc

/-- If `a ≤ b + c`, `b ≠ ∞`, and `c ≠ ∞`, then
`ENNReal.toReal a ≤ ENNReal.toReal b + ENNReal.toReal c`. This lemma is useful to transfer
triangle-like inequalities from `ENNReal`s to `Real`s. -/
/-
**ENNReal.toReal_le_add** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_le_add (hle : a <= b + c) (hb : b != ∞) (hc : c != ∞) : a.toReal <=
 b.toReal + c.toReal
参数：hle : a <= b + c；hb : b != ∞；hc : c != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toReal_le_add'`：toReal_le_add' (hle : a <= b + c) (hb : b = ∞ ->
 a = ∞) (hc : c = ∞ -> a = ∞) : a.toReal <= b.toReal + c.toReal

--- 原说明 ---
If `a ≤ b + c`, `b ≠ ∞`, and `c ≠ ∞`, then
`ENNReal.toReal a ≤ ENNReal.toReal b + ENNReal.toReal c`. This lemma is useful t
o transfer
triangle-like inequalities from `ENNReal`s to `Real`s.
-/
theorem toReal_le_add (hle : a ≤ b + c) (hb : b ≠ ∞) (hc : c ≠ ∞) :
    a.toReal ≤ b.toReal + c.toReal :=
  toReal_le_add' hle (flip absurd hb) (flip absurd hc)
/-
**ENNReal.not_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：not_lt_top {x : Real>=0∞} : ¬x < ∞ ↔ x = ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem not_lt_top {x : ℝ≥0∞} : ¬x < ∞ ↔ x = ∞ := by rw [lt_top_iff_ne_top, Classical.not_not]
/-
**ENNReal.add_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：add_ne_top : a + b != ∞ ↔ a != ∞ ∧ b != ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.add_lt_top`：∀ {a b : ENNReal}, a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤
-/
theorem add_ne_top : a + b ≠ ∞ ↔ a ≠ ∞ ∧ b ≠ ∞ := by simpa only [lt_top_iff_ne_top] using add_lt_top

@[aesop (rule_sets := [finiteness]) safe apply]
/-
**ENNReal.Finiteness.add_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal.Finiteness`。
形式化陈述：∀ {a b : ENNReal}, a ≠ ⊤ → b ≠ ⊤ → a + b ≠ ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.add_ne_top`：add_ne_top : a + b != ∞ ↔ a != ∞ ∧ b != ∞
-/
protected lemma Finiteness.add_ne_top {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) : a + b ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨ha, hb⟩
/-
**ENNReal.mul_top'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：mul_top' : a * ∞ = if a = 0 then 0 else ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
· 使用定理 `WithTop.mul_top'`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZ
eroClass α] (a : WithTop α), a * ⊤ = if a = 0 then 0 else ⊤
-/
theorem mul_top' : a * ∞ = if a = 0 then 0 else ∞ := by convert! WithTop.mul_top' a
/-
**ENNReal.mul_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal}, a ≠ 0 → a * ⊤ = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.mul_top`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZe
roClass α] {a : WithTop α}, a ≠ 0 → a * ⊤ = ⊤
-/
@[simp] theorem mul_top (h : a ≠ 0) : a * ∞ = ∞ := WithTop.mul_top h
/-
**ENNReal.top_mul'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：top_mul' : ∞ * a = if a = 0 then 0 else ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
· 使用定理 `WithTop.top_mul'`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZ
eroClass α] (b : WithTop α), ⊤ * b = if b = 0 then 0 else ⊤
-/
theorem top_mul' : ∞ * a = if a = 0 then 0 else ∞ := by convert! WithTop.top_mul' a
/-
**ENNReal.top_mul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal}, a ≠ 0 → ⊤ * a = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.top_mul`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZe
roClass α] {b : WithTop α}, b ≠ 0 → ⊤ * b = ⊤
-/
@[simp] theorem top_mul (h : a ≠ 0) : ∞ * a = ∞ := WithTop.top_mul h
/-
**ENNReal.top_mul_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：top_mul_top : ∞ * ∞ = ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.top_mul_top`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : M
ulZeroClass α], ⊤ * ⊤ = ⊤
-/
theorem top_mul_top : ∞ * ∞ = ∞ := WithTop.top_mul_top
/-
**ENNReal.mul_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：mul_eq_top : a * b = ∞ ↔ a != 0 ∧ b = ∞ ∨ a = ∞ ∧ b != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.mul_eq_top_iff`：mul_eq_top_iff : a * b = ⊤ ↔ a != 0 ∧ b = ⊤ ∨ a 
= ⊤ ∧ b != 0
-/
theorem mul_eq_top : a * b = ∞ ↔ a ≠ 0 ∧ b = ∞ ∨ a = ∞ ∧ b ≠ 0 :=
  WithTop.mul_eq_top_iff
/-
**ENNReal.mul_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.mul_lt_top`：mul_lt_top [LT α] {a b : WithTop α} (ha : a < ⊤) (hb
 : b < ⊤) : a * b < ⊤
-/
theorem mul_lt_top : a < ∞ → b < ∞ → a * b < ∞ := WithTop.mul_lt_top

-- This is unsafe because we could have `a = ∞` and `b = 0` or vice-versa
@[aesop (rule_sets := [finiteness]) unsafe 75% apply]
/-
**ENNReal.mul_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.mul_ne_top`：mul_ne_top {a b : WithTop α} (ha : a != ⊤) (hb : b !
= ⊤) : a * b != ⊤
-/
theorem mul_ne_top : a ≠ ∞ → b ≠ ∞ → a * b ≠ ∞ := WithTop.mul_ne_top
/-
**ENNReal.lt_top_of_mul_ne_top_left** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：lt_top_of_mul_ne_top_left (h : a * b != ∞) (hb : b != 0) : a < ∞
参数：h : a * b != ∞；hb : b != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `ENNReal.mul_eq_top`：mul_eq_top : a * b = ∞ ↔ a != 0 ∧ b = ∞ ∨ a = ∞ ∧ b 
!= 0
-/
theorem lt_top_of_mul_ne_top_left (h : a * b ≠ ∞) (hb : b ≠ 0) : a < ∞ :=
  lt_top_iff_ne_top.2 fun ha => h <| mul_eq_top.2 (Or.inr ⟨ha, hb⟩)
/-
**ENNReal.lt_top_of_mul_ne_top_right** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：lt_top_of_mul_ne_top_right (h : a * b != ∞) (ha : a != 0) : b < ∞
参数：h : a * b != ∞；ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.lt_top_of_mul_ne_top_left`：lt_top_of_mul_ne_top_left (h : a * b 
!= ∞) (hb : b != 0) : a < ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem lt_top_of_mul_ne_top_right (h : a * b ≠ ∞) (ha : a ≠ 0) : b < ∞ :=
  lt_top_of_mul_ne_top_left (by rwa [mul_comm]) ha
/-
**ENNReal.mul_lt_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：mul_lt_top_iff {a b : Real>=0∞} : a * b < ∞ ↔ a < ∞ ∧ b < ∞ ∨ a = 0 ∨ b = 
0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `or_assoc`：∀ {a b c : Prop}, (a ∨ b) ∨ c ↔ a ∨ b ∨ c
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `ENNReal.lt_top_of_mul_ne_top_left`：lt_top_of_mul_ne_top_left (h : a * b 
!= ∞) (hb : b != 0) : a < ∞
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ENNReal.lt_top_of_mul_ne_top_right`：lt_top_of_mul_ne_top_right (h : a * 
b != ∞) (ha : a != 0) : b < ∞
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem mul_lt_top_iff {a b : ℝ≥0∞} : a * b < ∞ ↔ a < ∞ ∧ b < ∞ ∨ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    rw [← or_assoc, or_iff_not_imp_right, or_iff_not_imp_right]
    intro hb ha
    exact ⟨lt_top_of_mul_ne_top_left h.ne hb, lt_top_of_mul_ne_top_right h.ne ha⟩
  · rintro (⟨ha, hb⟩ | rfl | rfl) <;> [exact mul_lt_top ha hb; simp; simp]
/-
**ENNReal.mul_self_lt_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：mul_self_lt_top_iff {a : Real>=0∞} : a * a < ⊤ ↔ a < ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.mul_lt_top_iff`：mul_lt_top_iff {a b : Real>=0∞} : a * b < ∞ ↔ a 
< ∞ ∧ b < ∞ ∨ a = 0 ∨ b = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_iff_left_iff_imp`：∀ {a b : Prop}, (a ∨ b ↔ a) ↔ b → a
· 使用定理 `ENNReal.zero_lt_top`：0 < ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mul_self_lt_top_iff {a : ℝ≥0∞} : a * a < ⊤ ↔ a < ⊤ := by
  rw [ENNReal.mul_lt_top_iff, and_self, or_self, or_iff_left_iff_imp]
  rintro rfl
  exact zero_lt_top
/-
**ENNReal.mul_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：mul_pos_iff : 0 < a * b ↔ 0 < a ∧ 0 < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanonicallyOrderedAdd.mul_pos`：∀ {R : Type u} [inst : CommSemiring R] [i
nst_1 : PartialOrder R] [CanonicallyOrderedAdd R] [NoZeroDivisors R] {a b : R}, 
  0 < a * b ↔ 0 < a…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
-/
theorem mul_pos_iff : 0 < a * b ↔ 0 < a ∧ 0 < b :=
  CanonicallyOrderedAdd.mul_pos
/-
**ENNReal.mul_pos** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：mul_pos (ha : a != 0) (hb : b != 0) : 0 < a * b
参数：ha : a != 0；hb : b != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.mul_pos_iff`：mul_pos_iff : 0 < a * b ↔ 0 < a ∧ 0 < b
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
theorem mul_pos (ha : a ≠ 0) (hb : b ≠ 0) : 0 < a * b :=
  mul_pos_iff.2 ⟨pos_iff_ne_zero.2 ha, pos_iff_ne_zero.2 hb⟩
/-
**ENNReal.top_pow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {n : ℕ}, n ≠ 0 → ⊤ ^ n = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.top_pow`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Monoi
dWithZero α] [inst_2 : NoZeroDivisors α] [inst_3 : Nontrivial α]   {n : ℕ}, n ≠ 
0 → ⊤…
· 使用定理 `NNReal.instNoZeroDivisors`：NoZeroDivisors NNReal
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
-/
@[simp] lemma top_pow {n : ℕ} (hn : n ≠ 0) : (∞ : ℝ≥0∞) ^ n = ∞ := WithTop.top_pow hn
/-
**ENNReal.pow_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal} {n : ℕ}, a ^ n = ⊤ ↔ a = ⊤ ∧ n ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.pow_eq_top_iff`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 
: MonoidWithZero α] [inst_2 : NoZeroDivisors α] [inst_3 : Nontrivial α]   {x : W
ithTop α} {n…
· 使用定理 `NNReal.instNoZeroDivisors`：NoZeroDivisors NNReal
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
-/
@[simp] lemma pow_eq_top_iff : a ^ n = ∞ ↔ a = ∞ ∧ n ≠ 0 := WithTop.pow_eq_top_iff
/-
**ENNReal.pow_ne_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：pow_ne_top_iff : a ^ n != ∞ ↔ a != ∞ ∨ n = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.pow_ne_top_iff`：pow_ne_top_iff : x ^ n != ⊤ ↔ x != ⊤ ∨ n = 0
· 使用定理 `NNReal.instNoZeroDivisors`：NoZeroDivisors NNReal
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
-/
lemma pow_ne_top_iff : a ^ n ≠ ∞ ↔ a ≠ ∞ ∨ n = 0 := WithTop.pow_ne_top_iff
/-
**ENNReal.pow_lt_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal} {n : ℕ}, a ^ n < ⊤ ↔ a < ⊤ ∨ n = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.pow_lt_top_iff`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 
: MonoidWithZero α] [inst_2 : NoZeroDivisors α] [inst_3 : Nontrivial α]   {x : W
ithTop α} {n…
· 使用定理 `NNReal.instNoZeroDivisors`：NoZeroDivisors NNReal
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
-/
@[simp] lemma pow_lt_top_iff : a ^ n < ∞ ↔ a < ∞ ∨ n = 0 := WithTop.pow_lt_top_iff
/-
**ENNReal.eq_top_of_pow** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：eq_top_of_pow (n : Nat) (ha : a ^ n = ∞) : a = ∞
参数：n : Nat；ha : a ^ n = ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.eq_top_of_pow`：eq_top_of_pow (n : Nat) (hx : x ^ n = ⊤) : x = ⊤
· 使用定理 `NNReal.instNoZeroDivisors`：NoZeroDivisors NNReal
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
-/
lemma eq_top_of_pow (n : ℕ) (ha : a ^ n = ∞) : a = ∞ := WithTop.eq_top_of_pow n ha

@[aesop (rule_sets := [finiteness]) safe apply]
/-
**ENNReal.pow_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：pow_ne_top (ha : a != ∞) : a ^ n != ∞
参数：ha : a != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.pow_ne_top`：pow_ne_top (hx : x != ⊤) : x ^ n != ⊤
· 使用定理 `NNReal.instNoZeroDivisors`：NoZeroDivisors NNReal
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
-/
lemma pow_ne_top (ha : a ≠ ∞) : a ^ n ≠ ∞ := WithTop.pow_ne_top ha
/-
**ENNReal.pow_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：pow_lt_top (ha : a < ∞) : a ^ n < ∞
参数：ha : a < ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.pow_lt_top`：pow_lt_top [Preorder α] (hx : x < ⊤) : x ^ n < ⊤
· 使用定理 `NNReal.instNoZeroDivisors`：NoZeroDivisors NNReal
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
-/
lemma pow_lt_top (ha : a < ∞) : a ^ n < ∞ := WithTop.pow_lt_top ha

end OperationsAndInfty

/-
**ENNReal.add_lt_add** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c d : ENNReal}, a < c → b < d → a + b < c + d
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.add_lt_add`：∀ {α : Type u} [inst : Add α] {w x y z : WithTop α} 
[inst_1 : Preorder α] [AddLeftStrictMono α] [AddRightStrictMono α],   x < z → y 
< w → x …
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
@[gcongr] protected theorem add_lt_add (ac : a < c) (bd : b < d) : a + b < c + d :=
  WithTop.add_lt_add ac bd

section Cancel

/-- An element `a` is `AddLECancellable` if `a + b ≤ a + c` implies `b ≤ c` for all `b` and `c`.
  This is true in `ℝ≥0∞` for all elements except `∞`. -/
@[simp]
/-
**ENNReal.addLECancellable_iff_ne** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：addLECancellable_iff_ne {a : Real>=0∞} : AddLECancellable a ↔ a != ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.addLECancellable_iff_ne_top`：addLECancellable_iff_ne_top [Nonemp
ty α] [Preorder α] [AddLeftReflectLE α] : AddLECancellable x ↔ x != ⊤ where mp
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G

--- 原说明 ---
An element `a` is `AddLECancellable` if `a + b ≤ a + c` implies `b ≤ c` for all 
`b` and `c`.
  This is true in `ℝ≥0∞` for all elements except `∞`.
-/
theorem addLECancellable_iff_ne {a : ℝ≥0∞} : AddLECancellable a ↔ a ≠ ∞ :=
  WithTop.addLECancellable_iff_ne_top

/-- This lemma has an abbreviated name because it is used frequently. -/
/-
**ENNReal.cancel_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：cancel_of_ne {a : Real>=0∞} (h : a != ∞) : AddLECancellable a
参数：h : a != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.addLECancellable_iff_ne`：addLECancellable_iff_ne {a : Real>=0∞} 
: AddLECancellable a ↔ a != ∞

--- 原说明 ---
This lemma has an abbreviated name because it is used frequently.
-/
theorem cancel_of_ne {a : ℝ≥0∞} (h : a ≠ ∞) : AddLECancellable a :=
  addLECancellable_iff_ne.mpr h

/-- This lemma has an abbreviated name because it is used frequently. -/
/-
**ENNReal.cancel_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：cancel_of_lt {a : Real>=0∞} (h : a < ∞) : AddLECancellable a
参数：h : a < ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.cancel_of_ne`：cancel_of_ne {a : Real>=0∞} (h : a != ∞) : AddLECa
ncellable a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b

--- 原说明 ---
This lemma has an abbreviated name because it is used frequently.
-/
theorem cancel_of_lt {a : ℝ≥0∞} (h : a < ∞) : AddLECancellable a :=
  cancel_of_ne h.ne

/-- This lemma has an abbreviated name because it is used frequently. -/
/-
**ENNReal.cancel_of_lt'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：cancel_of_lt' {a b : Real>=0∞} (h : a < b) : AddLECancellable a
参数：h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.cancel_of_ne`：cancel_of_ne {a : Real>=0∞} (h : a != ∞) : AddLECa
ncellable a
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤

--- 原说明 ---
This lemma has an abbreviated name because it is used frequently.
-/
theorem cancel_of_lt' {a b : ℝ≥0∞} (h : a < b) : AddLECancellable a :=
  cancel_of_ne h.ne_top

/-- This lemma has an abbreviated name because it is used frequently. -/
/-
**ENNReal.cancel_coe** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：cancel_coe {a : Real>=0} : AddLECancellable (a : Real>=0∞)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.cancel_of_ne`：cancel_of_ne {a : Real>=0∞} (h : a != ∞) : AddLECa
ncellable a
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞

--- 原说明 ---
This lemma has an abbreviated name because it is used frequently.
-/
theorem cancel_coe {a : ℝ≥0} : AddLECancellable (a : ℝ≥0∞) :=
  cancel_of_ne coe_ne_top
/-
**ENNReal.add_right_inj** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：add_right_inj (h : a != ∞) : a + b = a + c ↔ b = c
参数：h : a != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.inj`：∀ {α : Type u_1} [inst : Add α] [inst_1 : PartialO
rder α] {a b c : α}, AddLECancellable a → (a + b = a + c ↔ b = c)
· 使用定理 `ENNReal.cancel_of_ne`：cancel_of_ne {a : Real>=0∞} (h : a != ∞) : AddLECa
ncellable a
-/
theorem add_right_inj (h : a ≠ ∞) : a + b = a + c ↔ b = c :=
  (cancel_of_ne h).inj
/-
**ENNReal.add_left_inj** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：add_left_inj (h : a != ∞) : b + a = c + a ↔ b = c
参数：h : a != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.inj_left`：∀ {α : Type u_1} [inst : Add α] [IsAddCommuta
tive α] [inst_2 : PartialOrder α] {a b c : α},   AddLECancellable c → (a + c = b
 + c ↔ a = b)
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `ENNReal.cancel_of_ne`：cancel_of_ne {a : Real>=0∞} (h : a != ∞) : AddLECa
ncellable a
-/
theorem add_left_inj (h : a ≠ ∞) : b + a = c + a ↔ b = c :=
  (cancel_of_ne h).inj_left

end Cancel

section Sub

/-
**ENNReal.sub_eq_sInf** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：sub_eq_sInf {a b : Real>=0∞} : a - b = sInf { d | a <= d + b }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `le_tsub_add`：le_tsub_add : b <= b - a + a
-/
theorem sub_eq_sInf {a b : ℝ≥0∞} : a - b = sInf { d | a ≤ d + b } :=
  le_antisymm (le_sInf fun _ h => tsub_le_iff_right.mpr h) <| sInf_le <| mem_ofPred.2 le_tsub_add

/-- This is a special case of `WithTop.coe_sub` in the `ENNReal` namespace -/
/-
**ENNReal.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {r p : NNReal}, ↑(r - p) = ↑r - ↑p
参数：r - p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_sub`：coe_sub {a b : α} : (↑(a - b) : WithTop α) = ↑a - ↑b

--- 原说明 ---
This is a special case of `WithTop.coe_sub` in the `ENNReal` namespace
-/
@[simp, norm_cast] theorem coe_sub : (↑(r - p) : ℝ≥0∞) = ↑r - ↑p := WithTop.coe_sub

/-- This is a special case of `WithTop.top_sub_coe` in the `ENNReal` namespace -/
/-
**ENNReal.top_sub_coe** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {r : NNReal}, ⊤ - ↑r = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a special case of `WithTop.top_sub_coe` in the `ENNReal` namespace
-/
@[simp] theorem top_sub_coe : ∞ - ↑r = ∞ := rfl
/-
**ENNReal.top_sub** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal}, a ≠ ⊤ → ⊤ - a = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `ENNReal.top_sub_coe`：∀ {r : NNReal}, ⊤ - ↑r = ⊤

--- 原说明 ---
This is a special case of `WithTop.top_sub_coe` in the `ENNReal` namespace
-/
@[simp] lemma top_sub (ha : a ≠ ∞) : ∞ - a = ∞ := by lift a to ℝ≥0 using ha; exact top_sub_coe

/-- This is a special case of `WithTop.sub_top` in the `ENNReal` namespace -/
/-
**ENNReal.sub_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal}, a - ⊤ = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.sub_top`：sub_top {a : WithTop α} : a - ⊤ = (⊥ : α)

--- 原说明 ---
This is a special case of `WithTop.sub_top` in the `ENNReal` namespace
-/
@[simp] theorem sub_top : a - ∞ = 0 := WithTop.sub_top
/-
**ENNReal.sub_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, a - b = ⊤ ↔ a = ⊤ ∧ b ≠ ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.sub_eq_top_iff`：∀ {α : Type u_1} [inst : Sub α] [inst_1 : Bot α]
 {a b : WithTop α}, a - b = ⊤ ↔ a = ⊤ ∧ b ≠ ⊤

--- 原说明 ---
This is a special case of `WithTop.sub_top` in the `ENNReal` namespace
-/
@[simp] theorem sub_eq_top_iff : a - b = ∞ ↔ a = ∞ ∧ b ≠ ∞ := WithTop.sub_eq_top_iff
/-
**ENNReal.sub_ne_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：sub_ne_top_iff : a - b != ∞ ↔ a != ∞ ∨ b = ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.sub_ne_top_iff`：sub_ne_top_iff {a b : WithTop α} : a - b != ⊤ ↔ 
a != ⊤ ∨ b = ⊤

--- 原说明 ---
This is a special case of `WithTop.sub_top` in the `ENNReal` namespace
-/
lemma sub_ne_top_iff : a - b ≠ ∞ ↔ a ≠ ∞ ∨ b = ∞ := WithTop.sub_ne_top_iff

-- This is unsafe because we could have `a = b = ∞`
@[aesop (rule_sets := [finiteness]) unsafe 75% apply]
/-
**ENNReal.sub_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：sub_ne_top (ha : a != ∞) : a - b != ∞
参数：ha : a != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.sub_eq_top_iff`：∀ {a b : ENNReal}, a - b = ⊤ ↔ a = ⊤ ∧ b ≠ ⊤
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem sub_ne_top (ha : a ≠ ∞) : a - b ≠ ∞ := mt sub_eq_top_iff.mp <| mt And.left ha

@[simp, norm_cast]
/-
**ENNReal.natCast_sub** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：natCast_sub (m n : Nat) : ↑(m - n) = (m - n : Real>=0∞)
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_natCast`：coe_natCast (n : Nat) : ((n : Real>=0) : Real>=0∞) 
= n
· 使用定理 `Nat.cast_tsub`：cast_tsub [CommSemiring α] [PartialOrder α] [IsOrderedRin
g α] [CanonicallyOrderedAdd α] [Sub α] [OrderedSub α] [AddLeftReflectLE α] (m n 
: N…
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `NNReal.instOrderedSub`：OrderedSub NNReal
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `ENNReal.coe_sub`：∀ {r p : NNReal}, ↑(r - p) = ↑r - ↑p
-/
theorem natCast_sub (m n : ℕ) : ↑(m - n) = (m - n : ℝ≥0∞) := by
  rw [← coe_natCast, Nat.cast_tsub, coe_sub, coe_natCast, coe_natCast]

/-- See `ENNReal.sub_eq_of_eq_add'` for a version assuming that `a = c + b` itself is finite rather
than `b`. -/
/-
**ENNReal.sub_eq_of_eq_add** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, b ≠ ⊤ → a = c + b → a - b = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_eq_of_eq_add`：∀ {α : Type u_1} [inst : PartialOrde
r α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α}, 
  AddLECancellable b → a…
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `ENNReal.cancel_of_ne`：cancel_of_ne {a : Real>=0∞} (h : a != ∞) : AddLECa
ncellable a

--- 原说明 ---
See `ENNReal.sub_eq_of_eq_add'` for a version assuming that `a = c + b` itself i
s finite rather
than `b`.
-/
protected theorem sub_eq_of_eq_add (hb : b ≠ ∞) : a = c + b → a - b = c :=
  (cancel_of_ne hb).tsub_eq_of_eq_add

/-- Weaker version of `ENNReal.sub_eq_of_eq_add` assuming that `a = c + b` itself is finite rather
han `b`. -/
/-
**ENNReal.sub_eq_of_eq_add'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, a ≠ ⊤ → a = c + b → a - b = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_eq_of_eq_add'`：∀ {α : Type u_1} [inst : PartialOrd
er α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α} 
  [AddLeftMono α], AddLEC…
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `ENNReal.cancel_of_ne`：cancel_of_ne {a : Real>=0∞} (h : a != ∞) : AddLECa
ncellable a

--- 原说明 ---
Weaker version of `ENNReal.sub_eq_of_eq_add` assuming that `a = c + b` itself is
 finite rather
han `b`.
-/
protected lemma sub_eq_of_eq_add' (ha : a ≠ ∞) : a = c + b → a - b = c :=
  (cancel_of_ne ha).tsub_eq_of_eq_add'

/-- See `ENNReal.eq_sub_of_add_eq'` for a version assuming that `b = a + c` itself is finite rather
than `c`. -/
/-
**ENNReal.eq_sub_of_add_eq** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, c ≠ ⊤ → a + c = b → a = b - c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.eq_tsub_of_add_eq`：∀ {α : Type u_1} [inst : PartialOrde
r α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α}, 
  AddLECancellable c → a…
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `ENNReal.cancel_of_ne`：cancel_of_ne {a : Real>=0∞} (h : a != ∞) : AddLECa
ncellable a

--- 原说明 ---
See `ENNReal.eq_sub_of_add_eq'` for a version assuming that `b = a + c` itself i
s finite rather
than `c`.
-/
protected theorem eq_sub_of_add_eq (hc : c ≠ ∞) : a + c = b → a = b - c :=
  (cancel_of_ne hc).eq_tsub_of_add_eq

/-- Weaker version of `ENNReal.eq_sub_of_add_eq` assuming that `b = a + c` itself is finite rather
than `c`. -/
/-
**ENNReal.eq_sub_of_add_eq'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, b ≠ ⊤ → a + c = b → a = b - c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.eq_tsub_of_add_eq'`：∀ {α : Type u_1} [inst : PartialOrd
er α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α} 
  [AddLeftMono α], AddLEC…
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `ENNReal.cancel_of_ne`：cancel_of_ne {a : Real>=0∞} (h : a != ∞) : AddLECa
ncellable a

--- 原说明 ---
Weaker version of `ENNReal.eq_sub_of_add_eq` assuming that `b = a + c` itself is
 finite rather
than `c`.
-/
protected lemma eq_sub_of_add_eq' (hb : b ≠ ∞) : a + c = b → a = b - c :=
  (cancel_of_ne hb).eq_tsub_of_add_eq'

/-- See `ENNReal.sub_eq_of_eq_add_rev'` for a version assuming that `a = b + c` itself is finite
rather than `b`. -/
/-
**ENNReal.sub_eq_of_eq_add_rev** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, b ≠ ⊤ → a = b + c → a - b = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_eq_of_eq_add_rev`：∀ {α : Type u_1} [inst : Partial
Order α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : 
α},   AddLECancellable b → a…
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `ENNReal.cancel_of_ne`：cancel_of_ne {a : Real>=0∞} (h : a != ∞) : AddLECa
ncellable a

--- 原说明 ---
See `ENNReal.sub_eq_of_eq_add_rev'` for a version assuming that `a = b + c` itse
lf is finite
rather than `b`.
-/
protected theorem sub_eq_of_eq_add_rev (hb : b ≠ ∞) : a = b + c → a - b = c :=
  (cancel_of_ne hb).tsub_eq_of_eq_add_rev

/-- Weaker version of `ENNReal.sub_eq_of_eq_add_rev` assuming that `a = b + c` itself is finite
rather than `b`. -/
/-
**ENNReal.sub_eq_of_eq_add_rev'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, a ≠ ⊤ → a = b + c → a - b = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_eq_of_eq_add_rev'`：∀ {α : Type u_1} [inst : Partia
lOrder α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c :
 α}   [AddLeftMono α], AddLEC…
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `ENNReal.cancel_of_ne`：cancel_of_ne {a : Real>=0∞} (h : a != ∞) : AddLECa
ncellable a

--- 原说明 ---
Weaker version of `ENNReal.sub_eq_of_eq_add_rev` assuming that `a = b + c` itsel
f is finite
rather than `b`.
-/
protected lemma sub_eq_of_eq_add_rev' (ha : a ≠ ∞) : a = b + c → a - b = c :=
  (cancel_of_ne ha).tsub_eq_of_eq_add_rev'
/-
**ENNReal.add_sub_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, a ≠ ⊤ → a + b - a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddLECancellable.add_tsub_cancel_left`：∀ {α : Type u_1} [inst : PartialO
rder α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b : α},
   AddLECancellable a → a +…
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem add_sub_cancel_left (ha : a ≠ ∞) : a + b - a = b := by
  simp [ha]
/-
**ENNReal.add_sub_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, b ≠ ⊤ → a + b - b = a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddLECancellable.add_tsub_cancel_right`：∀ {α : Type u_1} [inst : Partial
Order α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b : α}
,   AddLECancellable b → a +…
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem add_sub_cancel_right (hb : b ≠ ∞) : a + b - b = a := by
  simp [hb]
/-
**ENNReal.sub_add_eq_add_sub** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, b ≤ a → b ≠ ⊤ → a - b + c = a + c - b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.eq_sub_of_add_eq`：∀ {a b c : ENNReal}, c ≠ ⊤ → a + c = b → a = b
 - c
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.add_left_inj`：add_left_inj (h : a != ∞) : b + a = c + a ↔ b = c
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
-/
protected theorem sub_add_eq_add_sub (hab : b ≤ a) (b_ne_top : b ≠ ∞) :
    a - b + c = a + c - b := by
  by_cases c_top : c = ∞
  · simpa [c_top] using! ENNReal.eq_sub_of_add_eq b_ne_top rfl
  refine ENNReal.eq_sub_of_add_eq b_ne_top ?_
  simp only [add_assoc, add_comm c b]
  simpa only [← add_assoc] using! (add_left_inj c_top).mpr <| tsub_add_cancel_of_le hab
/-
**ENNReal.add_sub_add_eq_sub_right** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：add_sub_add_eq_sub_right (hc : c != ∞
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.top_sub`：∀ {a : ENNReal}, a ≠ ⊤ → ⊤ - a = ⊤
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENNReal.sub_top`：∀ {a : ENNReal}, a - ⊤ = 0
· 使用定理 `add_tsub_add_eq_tsub_right`：add_tsub_add_eq_tsub_right (a c b : α) : a +
 c - (b + c) = a - b
· 使用定理 `NNReal.instOrderedSub`：OrderedSub NNReal
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
-/
lemma add_sub_add_eq_sub_right (hc : c ≠ ∞ := by finiteness) : (a + c) - (b + c) = a - b := by
  lift c to ℝ≥0 using hc
  cases a <;> cases b
  · simp
  · simp
  · simp
  · norm_cast
    rw [add_tsub_add_eq_tsub_right]
/-
**ENNReal.add_sub_add_eq_sub_left** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：add_sub_add_eq_sub_left (hc : c != ∞
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `ENNReal.add_sub_add_eq_sub_right`：add_sub_add_eq_sub_right (hc : c != ∞
-/
lemma add_sub_add_eq_sub_left (hc : c ≠ ∞ := by finiteness) : (c + a) - (c + b) = a - b := by
  simp_rw [add_comm c]
  exact ENNReal.add_sub_add_eq_sub_right hc
/-
**ENNReal.lt_add_of_sub_lt_left** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, a ≠ ⊤ ∨ b ≠ ⊤ → a - b < c → a < b + c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddLECancellable.lt_add_of_tsub_lt_left`：∀ {α : Type u_1} [inst : Partia
lOrder α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c :
 α},   AddLECancellable b → a…
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `ENNReal.cancel_of_ne`：cancel_of_ne {a : Real>=0∞} (h : a != ∞) : AddLECa
ncellable a
-/
protected theorem lt_add_of_sub_lt_left (h : a ≠ ∞ ∨ b ≠ ∞) : a - b < c → a < b + c := by
  obtain rfl | hb := eq_or_ne b ∞
  · rw [top_add, lt_top_iff_ne_top]
    exact fun _ => h.resolve_right (Classical.not_not.2 rfl)
  · exact (cancel_of_ne hb).lt_add_of_tsub_lt_left
/-
**ENNReal.lt_add_of_sub_lt_right** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, a ≠ ⊤ ∨ c ≠ ⊤ → a - c < b → a < b + c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.lt_add_of_sub_lt_left`：∀ {a b c : ENNReal}, a ≠ ⊤ ∨ b ≠ ⊤ → a - 
b < c → a < b + c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
protected theorem lt_add_of_sub_lt_right (h : a ≠ ∞ ∨ c ≠ ∞) : a - c < b → a < b + c :=
  add_comm c b ▸ ENNReal.lt_add_of_sub_lt_left h
/-
**ENNReal.le_sub_of_add_le_left** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：le_sub_of_add_le_left (ha : a != ∞) : a + b <= c -> b <= c - a
参数：ha : a != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.le_tsub_of_add_le_left`：∀ {α : Type u_1} [inst : Preord
er α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α},
   AddLECancellable a → a + b…
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `ENNReal.cancel_of_ne`：cancel_of_ne {a : Real>=0∞} (h : a != ∞) : AddLECa
ncellable a
-/
theorem le_sub_of_add_le_left (ha : a ≠ ∞) : a + b ≤ c → b ≤ c - a :=
  (cancel_of_ne ha).le_tsub_of_add_le_left
/-
**ENNReal.le_sub_of_add_le_right** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：le_sub_of_add_le_right (hb : b != ∞) : a + b <= c -> a <= c - b
参数：hb : b != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.le_tsub_of_add_le_right`：∀ {α : Type u_1} [inst : Preor
der α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α}
,   AddLECancellable b → a + b…
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `ENNReal.cancel_of_ne`：cancel_of_ne {a : Real>=0∞} (h : a != ∞) : AddLECa
ncellable a
-/
theorem le_sub_of_add_le_right (hb : b ≠ ∞) : a + b ≤ c → a ≤ c - b :=
  (cancel_of_ne hb).le_tsub_of_add_le_right
/-
**ENNReal.sub_lt_of_lt_add** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, c ≤ a → a < b + c → a - c < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddLECancellable.tsub_lt_iff_right`：∀ {α : Type u_1} [inst : AddCommSemi
group α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [inst_4 :
 Sub α] [OrderedSub α] {…
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `ENNReal.cancel_of_lt'`：cancel_of_lt' {a b : Real>=0∞} (h : a < b) : AddL
ECancellable a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
-/
protected theorem sub_lt_of_lt_add (hac : c ≤ a) (h : a < b + c) : a - c < b :=
  ((cancel_of_lt' <| hac.trans_lt h).tsub_lt_iff_right hac).mpr h
/-
**ENNReal.sub_lt_iff_lt_right** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, b ≠ ⊤ → b ≤ a → (a - b < c ↔ a < c + b)
参数：a - b < c ↔ a < c + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_lt_iff_right`：∀ {α : Type u_1} [inst : AddCommSemi
group α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [inst_4 :
 Sub α] [OrderedSub α] {…
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `ENNReal.cancel_of_ne`：cancel_of_ne {a : Real>=0∞} (h : a != ∞) : AddLECa
ncellable a
-/
protected theorem sub_lt_iff_lt_right (hb : b ≠ ∞) (hab : b ≤ a) : a - b < c ↔ a < c + b :=
  (cancel_of_ne hb).tsub_lt_iff_right hab
/-
**ENNReal.sub_lt_iff_lt_left** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, b ≠ ⊤ → b ≤ a → (a - b < c ↔ a < b + c)
参数：a - b < c ↔ a < b + c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_lt_iff_left`：∀ {α : Type u_1} [inst : AddCommSemig
roup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [inst_4 : 
Sub α] [OrderedSub α] {…
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `ENNReal.cancel_of_ne`：cancel_of_ne {a : Real>=0∞} (h : a != ∞) : AddLECa
ncellable a
-/
protected theorem sub_lt_iff_lt_left (hb : b ≠ ∞) (hab : b ≤ a) : a - b < c ↔ a < b + c :=
  (cancel_of_ne hb).tsub_lt_iff_left hab
/-
**ENNReal.le_sub_iff_add_le_left** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：le_sub_iff_add_le_left (hc : c != ∞) (hcb : c <= b) : a <= b - c ↔ c + a <
= b
参数：hc : c != ∞；hcb : c <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_le_of_le_tsub_left_of_le`：add_le_of_le_tsub_left_of_le (h : a <= c) 
(h2 : b <= c - a) : a + b <= c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `ENNReal.le_sub_of_add_le_left`：le_sub_of_add_le_left (ha : a != ∞) : a +
 b <= c -> b <= c - a
-/
theorem le_sub_iff_add_le_left (hc : c ≠ ∞) (hcb : c ≤ b) : a ≤ b - c ↔ c + a ≤ b :=
  ⟨fun h ↦ add_le_of_le_tsub_left_of_le hcb h, le_sub_of_add_le_left hc⟩
/-
**ENNReal.le_sub_iff_add_le_right** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：le_sub_iff_add_le_right (hc : c != ∞) (hcb : c <= b) : a <= b - c ↔ a + c 
<= b
参数：hc : c != ∞；hcb : c <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_le_of_le_tsub_right_of_le`：add_le_of_le_tsub_right_of_le (h : b <= c
) (h2 : a <= c - b) : a + b <= c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `ENNReal.le_sub_of_add_le_right`：le_sub_of_add_le_right (hb : b != ∞) : a
 + b <= c -> a <= c - b
-/
theorem le_sub_iff_add_le_right (hc : c ≠ ∞) (hcb : c ≤ b) : a ≤ b - c ↔ a + c ≤ b :=
  ⟨fun h ↦ add_le_of_le_tsub_right_of_le hcb h, le_sub_of_add_le_right hc⟩
/-
**ENNReal.sub_lt_self** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, a ≠ ⊤ → a ≠ 0 → b ≠ 0 → a - b < a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_lt_self`：∀ {α : Type u_1} [inst : AddCommMonoid α]
 [inst_1 : LinearOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]   [OrderedS
ub α] {a b : α}, Ad…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `ENNReal.cancel_of_ne`：cancel_of_ne {a : Real>=0∞} (h : a != ∞) : AddLECa
ncellable a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
protected theorem sub_lt_self (ha : a ≠ ∞) (ha₀ : a ≠ 0) (hb : b ≠ 0) : a - b < a :=
  (cancel_of_ne ha).tsub_lt_self (pos_iff_ne_zero.2 ha₀) (pos_iff_ne_zero.2 hb)
/-
**ENNReal.sub_lt_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, a ≠ ⊤ → (a - b < a ↔ 0 < a ∧ 0 < b)
参数：a - b < a ↔ 0 < a ∧ 0 < b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_lt_self_iff`：∀ {α : Type u_1} [inst : AddCommMonoi
d α] [inst_1 : LinearOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]   [Orde
redSub α] {a b : α}, Ad…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `ENNReal.cancel_of_ne`：cancel_of_ne {a : Real>=0∞} (h : a != ∞) : AddLECa
ncellable a
-/
protected theorem sub_lt_self_iff (ha : a ≠ ∞) : a - b < a ↔ 0 < a ∧ 0 < b :=
  (cancel_of_ne ha).tsub_lt_self_iff
/-
**ENNReal.sub_lt_of_sub_lt** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：sub_lt_of_sub_lt (h₂ : c <= a) (h₃ : a != ∞ ∨ b != ∞) (h₁ : a - b < c) : a
 - c < b
参数：h₂ : c <= a；h₃ : a != ∞ ∨ b != ∞；h₁ : a - b < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.sub_lt_of_lt_add`：∀ {a b c : ENNReal}, c ≤ a → a < b + c → a - c
 < b
· 使用定理 `ENNReal.lt_add_of_sub_lt_right`：∀ {a b c : ENNReal}, a ≠ ⊤ ∨ c ≠ ⊤ → a -
 c < b → a < b + c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem sub_lt_of_sub_lt (h₂ : c ≤ a) (h₃ : a ≠ ∞ ∨ b ≠ ∞) (h₁ : a - b < c) : a - c < b :=
  ENNReal.sub_lt_of_lt_add h₂ (add_comm c b ▸ ENNReal.lt_add_of_sub_lt_right h₃ h₁)
/-
**ENNReal.sub_sub_cancel** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：sub_sub_cancel (h : a != ∞) (h2 : b <= a) : a - (a - b) = b
参数：h : a != ∞；h2 : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_tsub_cancel_of_le`：∀ {α : Type u_1} [inst : AddCom
mSemigroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [ins
t_4 : Sub α] [OrderedSub α] {…
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `ENNReal.cancel_of_ne`：cancel_of_ne {a : Real>=0∞} (h : a != ∞) : AddLECa
ncellable a
· 使用定理 `ENNReal.sub_ne_top`：sub_ne_top (ha : a != ∞) : a - b != ∞
-/
theorem sub_sub_cancel (h : a ≠ ∞) (h2 : b ≤ a) : a - (a - b) = b :=
  (cancel_of_ne <| sub_ne_top h).tsub_tsub_cancel_of_le h2
/-
**ENNReal.sub_right_inj** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：sub_right_inj {a b c : Real>=0∞} (ha : a != ∞) (hb : b <= a) (hc : c <= a)
 : a - b = a - c ↔ b = c
参数：ha : a != ∞；hb : b <= a；hc : c <= a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_right_inj`：∀ {α : Type u_1} [inst : AddCommMonoid 
α] [inst_1 : PartialOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]   [Order
edSub α] {a b c : α},…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `ENNReal.cancel_of_ne`：cancel_of_ne {a : Real>=0∞} (h : a != ∞) : AddLECa
ncellable a
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
-/
theorem sub_right_inj {a b c : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≤ a) (hc : c ≤ a) :
    a - b = a - c ↔ b = c :=
  (cancel_of_ne ha).tsub_right_inj (cancel_of_ne <| ne_top_of_le_ne_top ha hb)
    (cancel_of_ne <| ne_top_of_le_ne_top ha hc) hb hc
/-
**ENNReal.sub_mul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, (0 < b → b < a → c ≠ ⊤) → (a - b) * c = a * c - b * c
参数：0 < b → b < a → c ≠ ⊤；a - b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `tsub_eq_zero_of_le`：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : 
PartialOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]   [OrderedSub α] {a b
 : α}, a…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `mul_left_mono`：mul_left_mono [MulRightMono α] {a : α} : Monotone (· * a)
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddLECancellable.tsub_mul`：∀ {R : Type u} [inst : NonUnitalNonAssocSemir
ing R] [inst_1 : PartialOrder R] [CanonicallyOrderedAdd R] [inst_3 : Sub R]   [O
rderedSub R] [S…
· 使用定理 `ENNReal.cancel_of_ne`：cancel_of_ne {a : Real>=0∞} (h : a != ∞) : AddLECa
ncellable a
· 使用定理 `ENNReal.mul_ne_top`：mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
-/
protected theorem sub_mul (h : 0 < b → b < a → c ≠ ∞) : (a - b) * c = a * c - b * c := by
  rcases le_or_gt a b with hab | hab; · simp [hab, mul_left_mono hab, tsub_eq_zero_of_le]
  rcases eq_zero_or_pos b with (rfl | hb); · simp
  exact (cancel_of_ne <| mul_ne_top hab.ne_top (h hb hab)).tsub_mul
/-
**ENNReal.mul_sub** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, (0 < c → c < b → a ≠ ⊤) → a * (b - c) = a * b - a * c
参数：0 < c → c < b → a ≠ ⊤；b - c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ENNReal.sub_mul`：∀ {a b c : ENNReal}, (0 < b → b < a → c ≠ ⊤) → (a - b) 
* c = a * c - b * c
-/
protected theorem mul_sub (h : 0 < c → c < b → a ≠ ∞) : a * (b - c) = a * b - a * c := by
  simp only [mul_comm a]
  exact ENNReal.sub_mul h
/-
**ENNReal.sub_le_sub_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：sub_le_sub_iff_left (h : c <= a) (h' : a != ∞) : (a - b <= a - c) ↔ c <= b
参数：h : c <= a；h' : a != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_le_tsub_iff_left`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]  
 [OrderedSub α] {a b c : α},…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `ENNReal.cancel_of_ne`：cancel_of_ne {a : Real>=0∞} (h : a != ∞) : AddLECa
ncellable a
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
-/
theorem sub_le_sub_iff_left (h : c ≤ a) (h' : a ≠ ∞) :
    (a - b ≤ a - c) ↔ c ≤ b :=
  (cancel_of_ne h').tsub_le_tsub_iff_left (cancel_of_ne (ne_top_of_le_ne_top h' h)) h
/-
**ENNReal.le_toReal_sub** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：le_toReal_sub {a b : Real>=0∞} (hb : b != ∞) : a.toReal - b.toReal <= (a -
 b).toReal
参数：hb : b != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `ENNReal.top_sub`：∀ {a : ENNReal}, a ≠ ⊤ → ⊤ - a = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
-/
theorem le_toReal_sub {a b : ℝ≥0∞} (hb : b ≠ ∞) : a.toReal - b.toReal ≤ (a - b).toReal := by
  lift b to ℝ≥0 using hb
  induction a
  · simp
  · simp only [← coe_sub, NNReal.sub_def, Real.coe_toNNReal', coe_toReal]
    exact le_max_left _ _

@[simp]
/-
**ENNReal.toNNReal_sub** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：toNNReal_sub (hb : b != ∞) : (a - b).toNNReal = a.toNNReal - b.toNNReal
参数：hb : b != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.top_sub`：∀ {a : ENNReal}, a ≠ ⊤ → ⊤ - a = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `NNReal.instOrderedSub`：OrderedSub NNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma toNNReal_sub (hb : b ≠ ∞) : (a - b).toNNReal = a.toNNReal - b.toNNReal := by
  lift b to ℝ≥0 using hb; induction a <;> simp [← coe_sub]

@[simp]
/-
**ENNReal.toReal_sub_of_le** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：toReal_sub_of_le (hba : b <= a) (ha : a != ∞) : (a - b).toReal = a.toReal 
- b.toReal
参数：hba : b <= a；ha : a != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ENNReal.toNNReal_sub`：toNNReal_sub (hb : b != ∞) : (a - b).toNNReal = a.
toNNReal - b.toNNReal
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `NNReal.coe_sub`：∀ {r₁ r₂ : NNReal}, r₂ ≤ r₁ → ↑(r₁ - r₂) = ↑r₁ - ↑r₂
· 使用定理 `ENNReal.toNNReal_mono`：toNNReal_mono (hb : b != ∞) (h : a <= b) : a.toNN
Real <= b.toNNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toReal_sub_of_le (hba : b ≤ a) (ha : a ≠ ∞) : (a - b).toReal = a.toReal - b.toReal := by
  simp [ENNReal.toReal, ne_top_of_le_ne_top ha hba, toNNReal_mono ha hba]
/-
**ENNReal.ofReal_sub** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_sub (p : Real) {q : Real} (hq : 0 <= q) : ENNReal.ofReal (p - q) = 
ENNReal.ofReal p - ENNReal.ofReal q
参数：p : Real；hq : 0 <= q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal_of_nonpos`：∀ {p : ℝ}, p ≤ 0 → ENNReal.ofReal p = 0
· 使用定理 `sub_nonpos_of_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, a ≤ b → a - b ≤ 0
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `tsub_eq_zero_of_le`：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : 
PartialOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]   [OrderedSub α] {a b
 : α}, a…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
· 使用定理 `ENNReal.eq_sub_of_add_eq`：∀ {a b c : ENNReal}, c ≠ ⊤ → a + c = b → a = b
 - c
· 使用定理 `ENNReal.ofReal_ne_top`：ofReal_ne_top {r : Real} : ENNReal.ofReal r != ∞
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_add`：ofReal_add {p q : Real} (hp : 0 <= p) (hq : 0 <= q) 
: ENNReal.ofReal (p + q) = ENNReal.ofReal p + ENNReal.ofReal q
· 使用定理 `sub_nonneg_of_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, b ≤ a → 0 ≤ a - b
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
theorem ofReal_sub (p : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    ENNReal.ofReal (p - q) = ENNReal.ofReal p - ENNReal.ofReal q := by
  obtain h | h := le_total p q
  · rw [ofReal_of_nonpos (sub_nonpos_of_le h), tsub_eq_zero_of_le (ofReal_le_ofReal h)]
  refine ENNReal.eq_sub_of_add_eq ofReal_ne_top ?_
  rw [← ofReal_add (sub_nonneg_of_le h) hq, sub_add_cancel]
/-
**ENNReal.sub_sub_sub_cancel_left** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：sub_sub_sub_cancel_left (ha : a != ∞) (h : b <= a) : a - c - (a - b) = b -
 c
参数：ha : a != ∞；h : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.sub_top`：∀ {a : ENNReal}, a - ⊤ = 0
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_tsub_tsub_cancel_left`：tsub_tsub_tsub_cancel_left (h : b <= a) : a 
- c - (a - b) = b - c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `NNReal.instOrderedSub`：OrderedSub NNReal
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
-/
lemma sub_sub_sub_cancel_left (ha : a ≠ ∞) (h : b ≤ a) : a - c - (a - b) = b - c := by
  have hb : b ≠ ∞ := ne_top_of_le_ne_top ha h
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  cases c
  · simp
  · norm_cast
    rw [tsub_tsub_tsub_cancel_left]
    exact mod_cast h

end Sub

section Interval

variable {x y z : ℝ≥0∞} {ε ε₁ ε₂ : ℝ≥0∞} {s : Set ℝ≥0∞}

/-
**ENNReal.Ico_eq_Iio** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {y : ENNReal}, Set.Ico 0 y = Set.Iio y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ico_bot`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderBot α] 
{a : α}, Set.Ico ⊥ a = Set.Iio a
-/
protected theorem Ico_eq_Iio : Ico 0 y = Iio y :=
  Ico_bot
/-
**ENNReal.mem_Iio_self_add** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：mem_Iio_self_add : x != ∞ -> ε != 0 -> x in Iio (x + ε)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.lt_add_right`：lt_add_right (ha : a != ∞) (hb : b != 0) : a < a +
 b
-/
theorem mem_Iio_self_add : x ≠ ∞ → ε ≠ 0 → x ∈ Iio (x + ε) := fun xt ε0 => lt_add_right xt ε0
/-
**ENNReal.mem_Ioo_self_sub_add** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：mem_Ioo_self_sub_add : x != ∞ -> x != 0 -> ε₁ != 0 -> ε₂ != 0 -> x in Ioo 
(x - ε₁) (x + ε₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.sub_lt_self`：∀ {a b : ENNReal}, a ≠ ⊤ → a ≠ 0 → b ≠ 0 → a - b < 
a
· 使用定理 `ENNReal.lt_add_right`：lt_add_right (ha : a != ∞) (hb : b != 0) : a < a +
 b
-/
theorem mem_Ioo_self_sub_add : x ≠ ∞ → x ≠ 0 → ε₁ ≠ 0 → ε₂ ≠ 0 → x ∈ Ioo (x - ε₁) (x + ε₂) :=
  fun xt x0 ε0 ε0' => ⟨ENNReal.sub_lt_self xt x0 ε0, lt_add_right xt ε0'⟩

@[simp]
/-
**ENNReal.image_coe_Iic** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：image_coe_Iic (x : Real>=0) : (↑) '' Iic x = Iic (x : Real>=0∞)
参数：x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.image_coe_Iic`：image_coe_Iic : (some : α -> WithTop α) '' Iic a 
= Iic (a : WithTop α)
-/
theorem image_coe_Iic (x : ℝ≥0) : (↑) '' Iic x = Iic (x : ℝ≥0∞) := WithTop.image_coe_Iic

@[simp]
/-
**ENNReal.image_coe_Ici** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：image_coe_Ici (x : Real>=0) : (↑) '' Ici x = Ico ↑x ∞
参数：x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.image_coe_Ici`：image_coe_Ici : (some : α -> WithTop α) '' Ici a 
= Ico (a : WithTop α) ⊤
-/
theorem image_coe_Ici (x : ℝ≥0) : (↑) '' Ici x = Ico ↑x ∞ := WithTop.image_coe_Ici

@[simp]
/-
**ENNReal.image_coe_Iio** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：image_coe_Iio (x : Real>=0) : (↑) '' Iio x = Iio (x : Real>=0∞)
参数：x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.image_coe_Iio`：image_coe_Iio : (some : α -> WithTop α) '' Iio a 
= Iio (a : WithTop α)
-/
theorem image_coe_Iio (x : ℝ≥0) : (↑) '' Iio x = Iio (x : ℝ≥0∞) := WithTop.image_coe_Iio

@[simp]
/-
**ENNReal.image_coe_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：image_coe_Ioi (x : Real>=0) : (↑) '' Ioi x = Ioo ↑x ∞
参数：x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.image_coe_Ioi`：image_coe_Ioi : (some : α -> WithTop α) '' Ioi a 
= Ioo (a : WithTop α) ⊤
-/
theorem image_coe_Ioi (x : ℝ≥0) : (↑) '' Ioi x = Ioo ↑x ∞ := WithTop.image_coe_Ioi

@[simp]
/-
**ENNReal.image_coe_Icc** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：image_coe_Icc (x y : Real>=0) : (↑) '' Icc x y = Icc (x : Real>=0∞) y
参数：x y : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.image_coe_Icc`：image_coe_Icc : (some : α -> WithTop α) '' Icc a 
b = Icc (a : WithTop α) b
-/
theorem image_coe_Icc (x y : ℝ≥0) : (↑) '' Icc x y = Icc (x : ℝ≥0∞) y := WithTop.image_coe_Icc

@[simp]
/-
**ENNReal.image_coe_Ico** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：image_coe_Ico (x y : Real>=0) : (↑) '' Ico x y = Ico (x : Real>=0∞) y
参数：x y : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.image_coe_Ico`：image_coe_Ico : (some : α -> WithTop α) '' Ico a 
b = Ico (a : WithTop α) b
-/
theorem image_coe_Ico (x y : ℝ≥0) : (↑) '' Ico x y = Ico (x : ℝ≥0∞) y := WithTop.image_coe_Ico

@[simp]
/-
**ENNReal.image_coe_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：image_coe_Ioc (x y : Real>=0) : (↑) '' Ioc x y = Ioc (x : Real>=0∞) y
参数：x y : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.image_coe_Ioc`：image_coe_Ioc : (some : α -> WithTop α) '' Ioc a 
b = Ioc (a : WithTop α) b
-/
theorem image_coe_Ioc (x y : ℝ≥0) : (↑) '' Ioc x y = Ioc (x : ℝ≥0∞) y := WithTop.image_coe_Ioc

@[simp]
/-
**ENNReal.image_coe_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：image_coe_Ioo (x y : Real>=0) : (↑) '' Ioo x y = Ioo (x : Real>=0∞) y
参数：x y : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.image_coe_Ioo`：image_coe_Ioo : (some : α -> WithTop α) '' Ioo a 
b = Ioo (a : WithTop α) b
-/
theorem image_coe_Ioo (x y : ℝ≥0) : (↑) '' Ioo x y = Ioo (x : ℝ≥0∞) y := WithTop.image_coe_Ioo

@[simp]
/-
**ENNReal.image_coe_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：image_coe_uIcc (x y : Real>=0) : (↑) '' uIcc x y = uIcc (x : Real>=0∞) y
参数：x y : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.image_coe_Icc`：image_coe_Icc (x y : Real>=0) : (↑) '' Icc x y = 
Icc (x : Real>=0∞) y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_coe_uIcc (x y : ℝ≥0) : (↑) '' uIcc x y = uIcc (x : ℝ≥0∞) y := by simp [uIcc]

@[simp]
/-
**ENNReal.image_coe_uIoc** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：image_coe_uIoc (x y : Real>=0) : (↑) '' uIoc x y = uIoc (x : Real>=0∞) y
参数：x y : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.image_coe_Ioc`：image_coe_Ioc (x y : Real>=0) : (↑) '' Ioc x y = 
Ioc (x : Real>=0∞) y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_coe_uIoc (x y : ℝ≥0) : (↑) '' uIoc x y = uIoc (x : ℝ≥0∞) y := by simp [uIoc]

@[simp]
/-
**ENNReal.image_coe_uIoo** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：image_coe_uIoo (x y : Real>=0) : (↑) '' uIoo x y = uIoo (x : Real>=0∞) y
参数：x y : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.image_coe_Ioo`：image_coe_Ioo (x y : Real>=0) : (↑) '' Ioo x y = 
Ioo (x : Real>=0∞) y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_coe_uIoo (x y : ℝ≥0) : (↑) '' uIoo x y = uIoo (x : ℝ≥0∞) y := by simp [uIoo]

end Interval

section iInf

variable {ι : Sort*} {f g : ι → ℝ≥0∞}
variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

/-
**ENNReal.toNNReal_iInf** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toNNReal_iInf (hf : forall i, f i != ∞) : (iInf f).toNNReal = ⨅ i, (f i).t
oNNReal
参数：hf : forall i, f i != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_of_empty`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] [IsEmpty ι] (f : ι → α), iInf f = ⊤
· 使用定理 `ENNReal.toNNReal_top`：⊤.toNNReal = 0
· 使用定理 `NNReal.iInf_empty`：iInf_empty [IsEmpty ι] (f : ι -> Real>=0) : ⨅ i, f i 
= 0
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toNNReal_iInf (hf : ∀ i, f i ≠ ∞) : (iInf f).toNNReal = ⨅ i, (f i).toNNReal := by
  cases isEmpty_or_nonempty ι
  · rw [iInf_of_empty, toNNReal_top, NNReal.iInf_empty]
  · lift f to ι → ℝ≥0 using hf
    simp_rw [← coe_iInf, toNNReal_coe]
/-
**ENNReal.toNNReal_sInf** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toNNReal_sInf (s : Set Real>=0∞) (hs : forall r in s, r != ∞) : (sInf s).t
oNNReal = sInf (ENNReal.toNNReal '' s)
参数：s : Set Real>=0∞；hs : forall r in s, r != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `ENNReal.toNNReal_iInf`：toNNReal_iInf (hf : forall i, f i != ∞) : (iInf f
).toNNReal = ⨅ i, (f i).toNNReal
-/
theorem toNNReal_sInf (s : Set ℝ≥0∞) (hs : ∀ r ∈ s, r ≠ ∞) :
    (sInf s).toNNReal = sInf (ENNReal.toNNReal '' s) := by
  have hf : ∀ i, ((↑) : s → ℝ≥0∞) i ≠ ∞ := fun ⟨r, rs⟩ => hs r rs
  simpa only [← sInf_range, ← image_eq_range, Subtype.range_coe_subtype] using! (toNNReal_iInf hf)
/-
**ENNReal.toReal_iInf** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_iInf (hf : forall i, f i != ∞) : (iInf f).toReal = ⨅ i, (f i).toRea
l
参数：hf : forall i, f i != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toNNReal_iInf`：toNNReal_iInf (hf : forall i, f i != ∞) : (iInf f
).toNNReal = ⨅ i, (f i).toNNReal
· 使用定理 `NNReal.coe_iInf`：coe_iInf {ι : Sort*} (s : ι -> Real>=0) : (↑(⨅ i, s i) 
: Real) = ⨅ i, ↑(s i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toReal_iInf (hf : ∀ i, f i ≠ ∞) : (iInf f).toReal = ⨅ i, (f i).toReal := by
  simp only [ENNReal.toReal, toNNReal_iInf hf, NNReal.coe_iInf]

set_option backward.isDefEq.respectTransparency false in
/-
**ENNReal.toReal_sInf** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_sInf (s : Set Real>=0∞) (hf : forall r in s, r != ∞) : (sInf s).toR
eal = sInf (ENNReal.toReal '' s)
参数：s : Set Real>=0∞；hf : forall r in s, r != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toNNReal_sInf`：toNNReal_sInf (s : Set Real>=0∞) (hs : forall r i
n s, r != ∞) : (sInf s).toNNReal = sInf (ENNReal.toNNReal '' s)
· 使用定理 `NNReal.coe_sInf`：coe_sInf (s : Set Real>=0) : (↑(sInf s) : Real) = sInf 
(((↑) : Real>=0 -> Real) '' s)
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toReal_sInf (s : Set ℝ≥0∞) (hf : ∀ r ∈ s, r ≠ ∞) :
    (sInf s).toReal = sInf (ENNReal.toReal '' s) := by
  simp only [ENNReal.toReal, toNNReal_sInf s hf, NNReal.coe_sInf, Set.image_image]
/-
**ENNReal.ofReal_iInf** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {ι : Sort u_1} [Nonempty ι] (f : ι → ℝ), ENNReal.ofReal (⨅ i, f i) = ⨅ i
, ENNReal.ofReal (f i)
参数：f : ι → ℝ；⨅ i, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iInf_eq_bot`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLinearOrder
 α] {f : ι → α}, iInf f = ⊥ ↔ ∀ (b : α), ⊥ < b → ∃ i, f i < b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.ofReal_of_nonpos`：∀ {p : ℝ}, p ≤ 0 → ENNReal.ofReal p = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `Real.iInf_nonpos'`：iInf_nonpos' (hf : exists i, f i <= 0) : ⨅ i, f i <= 
0
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_iInf_iff`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] 
{f : ι → α} {a : α}, a ≤ iInf f ↔ ∀ (i : ι), a ≤ f i
· 使用定理 `ENNReal.le_ofReal_iff_toReal_le`：le_ofReal_iff_toReal_le {a : Real>=0∞} 
{b : Real} (ha : a != ∞) (hb : 0 <= b) : a <= ENNReal.ofReal b ↔ ENNReal.toReal 
a <= b
· 使用引理 `Real.iInf_nonneg`：iInf_nonneg (hf : forall i, 0 <= f i) : 0 <= iInf f
· 使用定理 `le_ciInf_iff`：le_ciInf_iff [Nonempty ι] {f : ι -> α} {a : α} (hf : BddBe
low (range f)) : a <= iInf f ↔ forall i, a <= f i
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
-/
@[simp] lemma ofReal_iInf [Nonempty ι] (f : ι → ℝ) :
    ENNReal.ofReal (⨅ i, f i) = ⨅ i, ENNReal.ofReal (f i) := by
  obtain ⟨i, hi⟩ | h := em (∃ i, f i ≤ 0)
  · rw [iInf_eq_bot.2 fun _ _ ↦ ⟨i, by simpa [ofReal_of_nonpos hi]⟩]
    simp [Real.iInf_nonpos' ⟨i, hi⟩]
  replace h i : 0 ≤ f i := le_of_not_ge fun hi ↦ h ⟨i, hi⟩
  refine eq_of_forall_le_iff fun a ↦ ?_
  obtain rfl | ha := eq_or_ne a ∞
  · simp
  rw [le_iInf_iff, le_ofReal_iff_toReal_le ha, le_ciInf_iff ⟨0, by simpa [mem_lowerBounds]⟩]
  · exact forall_congr' fun i ↦ (le_ofReal_iff_toReal_le ha (h _)).symm
  · exact Real.iInf_nonneg h
/-
**ENNReal.iInf_add** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：iInf_add : iInf f + a = ⨅ i, f i + a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem iInf_add : iInf f + a = ⨅ i, f i + a :=
  le_antisymm (le_iInf fun _ => add_le_add (iInf_le _ _) <| le_rfl)
    (tsub_le_iff_right.1 <| le_iInf fun _ => tsub_le_iff_right.2 <| iInf_le _ _)
/-
**ENNReal.sub_iInf** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：sub_iInf : (a - ⨅ i, f i) = ⨆ i, a - f i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `ENNReal.iInf_add`：iInf_add : iInf f + a = ⨅ i, f i + a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sub_iInf : (a - ⨅ i, f i) = ⨆ i, a - f i := by
  refine eq_of_forall_ge_iff fun c => ?_
  rw [tsub_le_iff_right, add_comm, iInf_add]
  simp [tsub_le_iff_right, add_comm]
/-
**ENNReal.sInf_add** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：sInf_add {s : Set Real>=0∞} : sInf s + a = ⨅ b in s, b + a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sInf_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] {s : Set α}, s
Inf s = ⨅ a ∈ s, a
· 使用定理 `ENNReal.iInf_add`：iInf_add : iInf f + a = ⨅ i, f i + a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sInf_add {s : Set ℝ≥0∞} : sInf s + a = ⨅ b ∈ s, b + a := by simp [sInf_eq_iInf, iInf_add]
/-
**ENNReal.add_iInf** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：add_iInf {a : Real>=0∞} : a + iInf f = ⨅ b, a + f b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `ENNReal.iInf_add`：iInf_add : iInf f + a = ⨅ i, f i + a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_iInf {a : ℝ≥0∞} : a + iInf f = ⨅ b, a + f b := by
  rw [add_comm, iInf_add]; simp [add_comm]
/-
**ENNReal.iInf_add_iInf** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：iInf_add_iInf (h : forall i j, exists k, f k + g k <= f i + g j) : iInf f 
+ iInf g = ⨅ a, f a + g a
参数：h : forall i j, exists k, f k + g k <= f i + g j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.iInf_add`：iInf_add : iInf f + a = ⨅ i, f i + a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.add_iInf`：add_iInf {a : Real>=0∞} : a + iInf f = ⨅ b, a + f b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
-/
theorem iInf_add_iInf (h : ∀ i j, ∃ k, f k + g k ≤ f i + g j) : iInf f + iInf g = ⨅ a, f a + g a :=
  suffices ⨅ a, f a + g a ≤ iInf f + iInf g from
    le_antisymm (le_iInf fun _ => add_le_add (iInf_le _ _) (iInf_le _ _)) this
  calc
    ⨅ a, f a + g a ≤ ⨅ (a) (a'), f a + g a' :=
      le_iInf₂ fun a a' => let ⟨k, h⟩ := h a a'; iInf_le_of_le k h
    _ = iInf f + iInf g := by simp_rw [iInf_add, add_iInf]
/-
**ENNReal.iInf_add_iInf_of_monotone** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：iInf_add_iInf_of_monotone {ι : Type*} [Preorder ι] [IsCodirectedOrder ι] {
f g : ι -> Real>=0∞} (hf : Monotone f) (hg : Monotone g) : iInf f + iInf g = ⨅ a
, f a + g a
参数：hf : Monotone f；hg : Monotone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.iInf_add_iInf`：iInf_add_iInf (h : forall i j, exists k, f k + g 
k <= f i + g j) : iInf f + iInf g = ⨅ a, f a + g a
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `exists_le_le`：∀ {α : Type u_1} [inst : LE α] [IsCodirectedOrder α] (a b 
: α), ∃ c ≤ a, c ≤ b
-/
lemma iInf_add_iInf_of_monotone {ι : Type*} [Preorder ι] [IsCodirectedOrder ι] {f g : ι → ℝ≥0∞}
    (hf : Monotone f) (hg : Monotone g) : iInf f + iInf g = ⨅ a, f a + g a :=
  iInf_add_iInf fun i j ↦ (exists_le_le i j).imp fun _k ⟨hi, hj⟩ ↦ by gcongr <;> apply_rules
/-
**ENNReal.add_iInf** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：add_iInf {a : Real>=0∞} : a + iInf f = ⨅ b, a + f b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `ENNReal.iInf_add`：iInf_add : iInf f + a = ⨅ i, f i + a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma add_iInf₂ {κ : ι → Sort*} (f : (i : ι) → κ i → ℝ≥0∞) :
    a + ⨅ (i) (j), f i j = ⨅ (i) (j), a + f i j := by
  simp [add_iInf]
/-
**ENNReal.iInf** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iInf₂_add {κ : ι → Sort*} (f : (i : ι) → κ i → ℝ≥0∞) :
    (⨅ (i) (j), f i j) + a = ⨅ (i) (j), f i j + a := by
  simp only [add_comm, add_iInf₂]
/-
**ENNReal.add_sInf** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：add_sInf {s : Set Real>=0∞} : a + sInf s = ⨅ b in s, a + b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sInf_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] {s : Set α}, s
Inf s = ⨅ a ∈ s, a
· 使用引理 `ENNReal.add_iInf₂`：add_iInf₂ {κ : ι -> Sort*} (f : (i : ι) -> κ i -> Rea
l>=0∞) : a + ⨅ (i) (j), f i j = ⨅ (i) (j), a + f i j
-/
lemma add_sInf {s : Set ℝ≥0∞} : a + sInf s = ⨅ b ∈ s, a + b := by
  rw [sInf_eq_iInf, add_iInf₂]

variable {κ : Sort*}
/-
**ENNReal.le_iInf_add_iInf** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：le_iInf_add_iInf {g : κ -> Real>=0∞} (h : forall i j, a <= f i + g j) : a 
<= iInf f + iInf g
参数：h : forall i j, a <= f i + g j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.iInf_add`：iInf_add : iInf f + a = ⨅ i, f i + a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.add_iInf`：add_iInf {a : Real>=0∞} : a + iInf f = ⨅ b, a + f b
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
-/
lemma le_iInf_add_iInf {g : κ → ℝ≥0∞} (h : ∀ i j, a ≤ f i + g j) :
    a ≤ iInf f + iInf g := by
  simp_rw [iInf_add, add_iInf]; exact le_iInf₂ h
/-
**ENNReal.le_iInf** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma le_iInf₂_add_iInf₂ {q₁ : ι → Sort*} {q₂ : κ → Sort*}
    {f : (i : ι) → q₁ i → ℝ≥0∞} {g : (k : κ) → q₂ k → ℝ≥0∞}
    (h : ∀ i pi k qk, a ≤ f i pi + g k qk) :
    a ≤ (⨅ (i) (qi), f i qi) + ⨅ (k) (qk), g k qk := by
  simp_rw [iInf₂_add, add_iInf₂]
  exact le_iInf₂ fun i hi => le_iInf₂ (h i hi)
/-
**ENNReal.iInf_gt_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (a : ENNReal), ⨅ b, ⨅ (_ : a < b), b = a
参数：a : ENNReal；_ : a < b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_of_forall_gt`：∀ {α : Type u_2} [inst : LinearOrder α] {a b : α}, (∀ (
c : α), a < c → b < c) → b ≤ a
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `iInf₂_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst
 : CompleteLattice α] {a : α} {f : (i : ι) → κ i → α} (i : ι)   (j : κ i), f i j
 ≤ a…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
@[simp] lemma iInf_gt_eq_self (a : ℝ≥0∞) : ⨅ b, ⨅ _ : a < b, b = a := by
  refine le_antisymm ?_ (le_iInf₂ fun b hb ↦ hb.le)
  refine le_of_forall_gt fun c hac ↦ ?_
  obtain ⟨d, had, hdc⟩ := exists_between hac
  exact (iInf₂_le_of_le d had le_rfl).trans_lt hdc
/-
**ENNReal.exists_add_lt_of_add_lt** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：exists_add_lt_of_add_lt {x y z : Real>=0∞} (h : y + z < x) : exists y' > y
, exists z' > z, y' + z' < x
参数：h : y + z < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `ENNReal.iInf_gt_eq_self`：∀ (a : ENNReal), ⨅ b, ⨅ (_ : a < b), b = a
· 使用引理 `ENNReal.le_iInf₂_add_iInf₂`：le_iInf₂_add_iInf₂ {q₁ : ι -> Sort*} {q₂ : κ
 -> Sort*} {f : (i : ι) -> q₁ i -> Real>=0∞} {g : (k : κ) -> q₂ k -> Real>=0∞} (
h : forall i pi …
-/
lemma exists_add_lt_of_add_lt {x y z : ℝ≥0∞} (h : y + z < x) :
    ∃ y' > y, ∃ z' > z, y' + z' < x := by
  contrapose! h
  simpa using le_iInf₂_add_iInf₂ h

end iInf

section iSup

variable {ι κ : Sort*} {f g : ι → ℝ≥0∞} {s : Set ℝ≥0∞} {a : ℝ≥0∞}

/-
**ENNReal.toNNReal_iSup** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toNNReal_iSup (hf : forall i, f i != ∞) : (iSup f).toNNReal = ⨆ i, (f i).t
oNNReal
参数：hf : forall i, f i != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_iSup`：coe_iSup {ι : Sort*} {f : ι -> Real>=0} (hf : BddAbove
 (range f)) : (↑(iSup f) : Real>=0∞) = ⨆ a, ↑(f a)
· 使用定理 `ENNReal.toNNReal_coe`：∀ (r : NNReal), (↑r).toNNReal = r
· 使用定理 `NNReal.iSup_of_not_bddAbove`：iSup_of_not_bddAbove (hf : ¬BddAbove (range
 f)) : ⨆ i, f i = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ENNReal.iSup_coe_eq_top`：iSup_coe_eq_top : ⨆ i, (f i : Real>=0∞) = ⊤ ↔ ¬
 BddAbove (range f)
· 使用定理 `ENNReal.toNNReal_top`：⊤.toNNReal = 0
-/
theorem toNNReal_iSup (hf : ∀ i, f i ≠ ∞) : (iSup f).toNNReal = ⨆ i, (f i).toNNReal := by
  lift f to ι → ℝ≥0 using hf
  simp_rw [toNNReal_coe]
  by_cases h : BddAbove (range f)
  · rw [← coe_iSup h, toNNReal_coe]
  · rw [NNReal.iSup_of_not_bddAbove h, iSup_coe_eq_top.2 h, toNNReal_top]
/-
**ENNReal.toNNReal_sSup** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toNNReal_sSup (s : Set Real>=0∞) (hs : forall r in s, r != ∞) : (sSup s).t
oNNReal = sSup (ENNReal.toNNReal '' s)
参数：s : Set Real>=0∞；hs : forall r in s, r != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `ENNReal.toNNReal_iSup`：toNNReal_iSup (hf : forall i, f i != ∞) : (iSup f
).toNNReal = ⨆ i, (f i).toNNReal
-/
theorem toNNReal_sSup (s : Set ℝ≥0∞) (hs : ∀ r ∈ s, r ≠ ∞) :
    (sSup s).toNNReal = sSup (ENNReal.toNNReal '' s) := by
  have hf : ∀ i, ((↑) : s → ℝ≥0∞) i ≠ ∞ := fun ⟨r, rs⟩ => hs r rs
  simpa only [← sSup_range, ← image_eq_range, Subtype.range_coe_subtype] using! (toNNReal_iSup hf)
/-
**ENNReal.toReal_iSup** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_iSup (hf : forall i, f i != ∞) : (iSup f).toReal = ⨆ i, (f i).toRea
l
参数：hf : forall i, f i != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toNNReal_iSup`：toNNReal_iSup (hf : forall i, f i != ∞) : (iSup f
).toNNReal = ⨆ i, (f i).toNNReal
· 使用定理 `NNReal.coe_iSup`：coe_iSup {ι : Sort*} (s : ι -> Real>=0) : (↑(⨆ i, s i) 
: Real) = ⨆ i, ↑(s i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toReal_iSup (hf : ∀ i, f i ≠ ∞) : (iSup f).toReal = ⨆ i, (f i).toReal := by
  simp only [ENNReal.toReal, toNNReal_iSup hf, NNReal.coe_iSup]

set_option backward.isDefEq.respectTransparency false in
/-
**ENNReal.toReal_sSup** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_sSup (s : Set Real>=0∞) (hf : forall r in s, r != ∞) : (sSup s).toR
eal = sSup (ENNReal.toReal '' s)
参数：s : Set Real>=0∞；hf : forall r in s, r != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toNNReal_sSup`：toNNReal_sSup (s : Set Real>=0∞) (hs : forall r i
n s, r != ∞) : (sSup s).toNNReal = sSup (ENNReal.toNNReal '' s)
· 使用定理 `NNReal.coe_sSup`：coe_sSup (s : Set Real>=0) : (↑(sSup s) : Real) = sSup 
(((↑) : Real>=0 -> Real) '' s)
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toReal_sSup (s : Set ℝ≥0∞) (hf : ∀ r ∈ s, r ≠ ∞) :
    (sSup s).toReal = sSup (ENNReal.toReal '' s) := by
  simp only [ENNReal.toReal, toNNReal_sSup s hf, NNReal.coe_sSup, Set.image_image]
/-
**ENNReal.iSup_sub** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：iSup_sub : (⨆ i, f i) - a = ⨆ i, f i - a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `tsub_le_tsub`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : AddCommSemi
group α] [inst_2 : Sub α] [OrderedSub α] {a b c d : α}   [AddLeftMono α], a ≤ b 
→ …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem iSup_sub : (⨆ i, f i) - a = ⨆ i, f i - a :=
  le_antisymm (tsub_le_iff_right.2 <| iSup_le fun i => tsub_le_iff_right.1 <| le_iSup (f · - a) i)
    (iSup_le fun _ => tsub_le_tsub (le_iSup _ _) (le_refl a))
/-
**ENNReal.iSup_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {ι : Sort u_1} {f : ι → ENNReal}, ⨆ i, f i = 0 ↔ ∀ (i : ι), f i = 0
参数：i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_eq_bot`：iSup_eq_bot : iSup s = ⊥ ↔ forall i, s i = ⊥
-/
@[simp] lemma iSup_eq_zero : ⨆ i, f i = 0 ↔ ∀ i, f i = 0 := iSup_eq_bot
/-
**ENNReal.iSup_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {ι : Sort u_1}, ⨆ x, 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma iSup_zero : ⨆ _ : ι, (0 : ℝ≥0∞) = 0 := by simp
/-
**ENNReal.iSup_natCast** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：iSup_natCast : ⨆ n : Nat, (n : Real>=0∞) = ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iSup_eq_top`：iSup_eq_top : iSup f = ⊤ ↔ forall b < ⊤, exists i, b < f i
· 使用定理 `ENNReal.exists_nat_gt`：∀ {r : ENNReal}, r ≠ ⊤ → ∃ n, r < ↑n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
-/
lemma iSup_natCast : ⨆ n : ℕ, (n : ℝ≥0∞) = ∞ :=
  iSup_eq_top.2 fun _b hb => ENNReal.exists_nat_gt (lt_top_iff_ne_top.1 hb)
/-
**ENNReal.add_iSup** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：add_iSup [Nonempty ι] (f : ι -> Real>=0∞) : a + ⨆ i, f i = ⨆ i, a + f i
参数：f : ι -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `add_le_of_le_tsub_left_of_le`：add_le_of_le_tsub_left_of_le (h : a <= c) 
(h2 : b <= c - a) : a + b <= c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `ENNReal.le_sub_of_add_le_left`：le_sub_of_add_le_left (ha : a != ∞) : a +
 b <= c -> b <= c - a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
lemma add_iSup [Nonempty ι] (f : ι → ℝ≥0∞) : a + ⨆ i, f i = ⨆ i, a + f i := by
  obtain rfl | ha := eq_or_ne a ∞
  · simp
  refine le_antisymm ?_ <| iSup_le fun i ↦ by grw [← le_iSup]
  refine add_le_of_le_tsub_left_of_le (le_iSup_of_le (Classical.arbitrary _) le_self_add) ?_
  exact iSup_le fun i ↦ ENNReal.le_sub_of_add_le_left ha <| le_iSup (a + f ·) i
/-
**ENNReal.iSup_add** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：iSup_add [Nonempty ι] (f : ι -> Real>=0∞) : (⨆ i, f i) + a = ⨆ i, f i + a
参数：f : ι -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `ENNReal.add_iSup`：add_iSup [Nonempty ι] (f : ι -> Real>=0∞) : a + ⨆ i, f
 i = ⨆ i, a + f i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iSup_add [Nonempty ι] (f : ι → ℝ≥0∞) : (⨆ i, f i) + a = ⨆ i, f i + a := by
  simp [add_comm, add_iSup]
/-
**ENNReal.add_biSup'** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：add_biSup' {p : ι -> Prop} (h : exists i, p i) (f : ι -> Real>=0∞) : a + ⨆
 i, ⨆ _ : p i, f i = ⨆ i, ⨆ _ : p i, a + f i
参数：h : exists i, p i；f : ι -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nonempty_subtype`：nonempty_subtype {α} {p : α -> Prop} : Nonempty (Subty
pe p) ↔ exists a : α, p a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
· 使用引理 `ENNReal.add_iSup`：add_iSup [Nonempty ι] (f : ι -> Real>=0∞) : a + ⨆ i, f
 i = ⨆ i, a + f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma add_biSup' {p : ι → Prop} (h : ∃ i, p i) (f : ι → ℝ≥0∞) :
    a + ⨆ i, ⨆ _ : p i, f i = ⨆ i, ⨆ _ : p i, a + f i := by
  have : Nonempty {i // p i} := nonempty_subtype.2 h
  simp only [iSup_subtype', add_iSup]
/-
**ENNReal.biSup_add'** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：biSup_add' {p : ι -> Prop} (h : exists i, p i) (f : ι -> Real>=0∞) : (⨆ i,
 ⨆ _ : p i, f i) + a = ⨆ i, ⨆ _ : p i, f i + a
参数：h : exists i, p i；f : ι -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `ENNReal.add_biSup'`：add_biSup' {p : ι -> Prop} (h : exists i, p i) (f : 
ι -> Real>=0∞) : a + ⨆ i, ⨆ _ : p i, f i = ⨆ i, ⨆ _ : p i, a + f i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma biSup_add' {p : ι → Prop} (h : ∃ i, p i) (f : ι → ℝ≥0∞) :
    (⨆ i, ⨆ _ : p i, f i) + a = ⨆ i, ⨆ _ : p i, f i + a := by simp only [add_comm, add_biSup' h]
/-
**ENNReal.add_biSup** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：add_biSup {ι : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι -> Real>=0∞) : 
a + ⨆ i in s, f i = ⨆ i in s, a + f i
参数：hs : s.Nonempty；f : ι -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.add_biSup'`：add_biSup' {p : ι -> Prop} (h : exists i, p i) (f : 
ι -> Real>=0∞) : a + ⨆ i, ⨆ _ : p i, f i = ⨆ i, ⨆ _ : p i, a + f i
-/
lemma add_biSup {ι : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι → ℝ≥0∞) :
    a + ⨆ i ∈ s, f i = ⨆ i ∈ s, a + f i := add_biSup' hs _
/-
**ENNReal.biSup_add** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：biSup_add {ι : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι -> Real>=0∞) : 
(⨆ i in s, f i) + a = ⨆ i in s, f i + a
参数：hs : s.Nonempty；f : ι -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.biSup_add'`：biSup_add' {p : ι -> Prop} (h : exists i, p i) (f : 
ι -> Real>=0∞) : (⨆ i, ⨆ _ : p i, f i) + a = ⨆ i, ⨆ _ : p i, f i + a
-/
lemma biSup_add {ι : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι → ℝ≥0∞) :
    (⨆ i ∈ s, f i) + a = ⨆ i ∈ s, f i + a := biSup_add' hs _
/-
**ENNReal.add_sSup** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：add_sSup (hs : s.Nonempty) : a + sSup s = ⨆ b in s, a + b
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用引理 `ENNReal.add_biSup`：add_biSup {ι : Type*} {s : Set ι} (hs : s.Nonempty) (
f : ι -> Real>=0∞) : a + ⨆ i in s, f i = ⨆ i in s, a + f i
-/
lemma add_sSup (hs : s.Nonempty) : a + sSup s = ⨆ b ∈ s, a + b := by
  rw [sSup_eq_iSup, add_biSup hs]
/-
**ENNReal.sSup_add** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：sSup_add (hs : s.Nonempty) : sSup s + a = ⨆ b in s, b + a
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用引理 `ENNReal.biSup_add`：biSup_add {ι : Type*} {s : Set ι} (hs : s.Nonempty) (
f : ι -> Real>=0∞) : (⨆ i in s, f i) + a = ⨆ i in s, f i + a
-/
lemma sSup_add (hs : s.Nonempty) : sSup s + a = ⨆ b ∈ s, b + a := by
  rw [sSup_eq_iSup, biSup_add hs]
/-
**ENNReal.iSup_add_iSup_le** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：iSup_add_iSup_le [Nonempty ι] [Nonempty κ] {g : κ -> Real>=0∞} (h : forall
 i j, f i + g j <= a) : iSup f + iSup g <= a
参数：h : forall i j, f i + g j <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ENNReal.iSup_add`：iSup_add [Nonempty ι] (f : ι -> Real>=0∞) : (⨆ i, f i)
 + a = ⨆ i, f i + a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ENNReal.add_iSup`：add_iSup [Nonempty ι] (f : ι -> Real>=0∞) : a + ⨆ i, f
 i = ⨆ i, a + f i
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
-/
lemma iSup_add_iSup_le [Nonempty ι] [Nonempty κ] {g : κ → ℝ≥0∞} (h : ∀ i j, f i + g j ≤ a) :
    iSup f + iSup g ≤ a := by simp_rw [iSup_add, add_iSup]; exact iSup₂_le h
/-
**ENNReal.biSup_add_biSup_le'** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：biSup_add_biSup_le' {p : ι -> Prop} {q : κ -> Prop} (hp : exists i, p i) (
hq : exists j, q j) {g : κ -> Real>=0∞} (h : forall i, p i -> forall j, q j -> f
 i + g j <= a) : (⨆ i, ⨆ _ : p i, f i) + ⨆ j, ⨆ _ : q j, g j <= a
参数：hp : exists i, p i；hq : exists j, q j；h : forall i, p i -> forall j, q j -> f
 i + g j <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ENNReal.biSup_add'`：biSup_add' {p : ι -> Prop} (h : exists i, p i) (f : 
ι -> Real>=0∞) : (⨆ i, ⨆ _ : p i, f i) + a = ⨆ i, ⨆ _ : p i, f i + a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `ENNReal.add_biSup'`：add_biSup' {p : ι -> Prop} (h : exists i, p i) (f : 
ι -> Real>=0∞) : a + ⨆ i, ⨆ _ : p i, f i = ⨆ i, ⨆ _ : p i, a + f i
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
-/
lemma biSup_add_biSup_le' {p : ι → Prop} {q : κ → Prop} (hp : ∃ i, p i) (hq : ∃ j, q j)
    {g : κ → ℝ≥0∞} (h : ∀ i, p i → ∀ j, q j → f i + g j ≤ a) :
    (⨆ i, ⨆ _ : p i, f i) + ⨆ j, ⨆ _ : q j, g j ≤ a := by
  simp_rw [biSup_add' hp, add_biSup' hq]
  exact iSup₂_le fun i hi => iSup₂_le (h i hi)
/-
**ENNReal.biSup_add_biSup_le** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：biSup_add_biSup_le {ι κ : Type*} {s : Set ι} {t : Set κ} (hs : s.Nonempty)
 (ht : t.Nonempty) {f : ι -> Real>=0∞} {g : κ -> Real>=0∞} {a : Real>=0∞} (h : f
orall i in s, forall j in t, f i + g j <= a) : (⨆ i in s, f i) + ⨆ j in t, g j <
= a
参数：hs : s.Nonempty；ht : t.Nonempty；h : forall i in s, forall j in t, f i + g j <
= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.biSup_add_biSup_le'`：biSup_add_biSup_le' {p : ι -> Prop} {q : κ 
-> Prop} (hp : exists i, p i) (hq : exists j, q j) {g : κ -> Real>=0∞} (h : fora
ll i, p i -> fora…
-/
lemma biSup_add_biSup_le {ι κ : Type*} {s : Set ι} {t : Set κ} (hs : s.Nonempty) (ht : t.Nonempty)
    {f : ι → ℝ≥0∞} {g : κ → ℝ≥0∞} {a : ℝ≥0∞} (h : ∀ i ∈ s, ∀ j ∈ t, f i + g j ≤ a) :
    (⨆ i ∈ s, f i) + ⨆ j ∈ t, g j ≤ a := biSup_add_biSup_le' hs ht h
/-
**ENNReal.iSup_add_iSup** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：iSup_add_iSup (h : forall i j, exists k, f i + g j <= f k + g k) : iSup f 
+ iSup g = ⨆ i, f i + g i
参数：h : forall i j, exists k, f i + g j <= f k + g k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ciSup_of_empty`：ciSup_of_empty [IsEmpty ι] (f : ι -> α) : ⨆ i, f i = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `ENNReal.iSup_add_iSup_le`：iSup_add_iSup_le [Nonempty ι] [Nonempty κ] {g 
: κ -> Real>=0∞} (h : forall i j, f i + g j <= a) : iSup f + iSup g <= a
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
lemma iSup_add_iSup (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) : iSup f + iSup g = ⨆ i, f i + g i := by
  cases isEmpty_or_nonempty ι
  · simp
  · refine le_antisymm ?_ (iSup_le fun a => add_le_add (le_iSup _ _) (le_iSup _ _))
    refine iSup_add_iSup_le fun i j => ?_
    rcases h i j with ⟨k, hk⟩
    exact le_iSup_of_le k hk
/-
**ENNReal.iSup_add_iSup_of_monotone** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：iSup_add_iSup_of_monotone {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {f 
g : ι -> Real>=0∞} (hf : Monotone f) (hg : Monotone g) : iSup f + iSup g = ⨆ a, 
f a + g a
参数：hf : Monotone f；hg : Monotone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.iSup_add_iSup`：iSup_add_iSup (h : forall i j, exists k, f i + g 
j <= f k + g k) : iSup f + iSup g = ⨆ i, f i + g i
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `exists_ge_ge`：exists_ge_ge [LE α] [IsDirectedOrder α] (a b : α) : exists
 c, a <= c ∧ b <= c
-/
lemma iSup_add_iSup_of_monotone {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {f g : ι → ℝ≥0∞}
    (hf : Monotone f) (hg : Monotone g) : iSup f + iSup g = ⨆ a, f a + g a :=
  iSup_add_iSup fun i j ↦ (exists_ge_ge i j).imp fun _k ⟨hi, hj⟩ ↦ by gcongr <;> apply_rules
/-
**ENNReal.sub_iSup** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：sub_iSup [Nonempty ι] (ha : a != ∞) : a - ⨆ i, f i = ⨅ i, a - f i
参数：ha : a != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_eq_zero_iff_le`：tsub_eq_zero_iff_le : a - b = 0 ↔ a <= b
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `iInf_eq_bot`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLinearOrder
 α] {f : ι → α}, iInf f = ⊥ ↔ ∀ (b : α), ⊥ < b → ∃ i, f i < b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `tsub_eq_zero_of_le`：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : 
PartialOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]   [OrderedSub α] {a b
 : α}, a…
· 使用定理 `ENNReal.bot_eq_zero`：bot_eq_zero : (⊥ : Real>=0∞) = 0
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `tsub_le_tsub_left`：tsub_le_tsub_left (h : a <= b) (c : α) : c - b <= c -
 a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `ENNReal.le_sub_of_add_le_left`：le_sub_of_add_le_left (ha : a != ∞) : a +
 b <= c -> b <= c - a
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `add_le_of_le_tsub_right_of_le`：add_le_of_le_tsub_right_of_le (h : b <= c
) (h2 : a <= c - b) : a + b <= c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `tsub_le_self`：tsub_le_self : a - b <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.sub_sub_cancel`：sub_sub_cancel (h : a != ∞) (h2 : b <= a) : a - 
(a - b) = b
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
-/
lemma sub_iSup [Nonempty ι] (ha : a ≠ ∞) : a - ⨆ i, f i = ⨅ i, a - f i := by
  obtain ⟨i, hi⟩ | h := em (∃ i, a < f i)
  · rw [tsub_eq_zero_iff_le.2 <| le_iSup_of_le _ hi.le, iInf_eq_bot.2, bot_eq_zero]
    exact fun x hx ↦ ⟨i, by simpa [hi.le, tsub_eq_zero_of_le]⟩
  simp_rw [not_exists, not_lt] at h
  refine le_antisymm (le_iInf fun i ↦ tsub_le_tsub_left (le_iSup ..) _) <|
    ENNReal.le_sub_of_add_le_left (ne_top_of_le_ne_top ha <| iSup_le h) <|
    add_le_of_le_tsub_right_of_le (iInf_le_of_le (Classical.arbitrary _) tsub_le_self) <|
    iSup_le fun i ↦ ?_
  rw [← sub_sub_cancel ha (h _)]
  exact tsub_le_tsub_left (iInf_le (a - f ·) i) _
/-
**ENNReal.iSup_lt_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (a : ENNReal), ⨆ b, ⨆ (_ : b < a), b = a
参数：a : ENNReal；_ : b < a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_of_forall_lt`：le_of_forall_lt (H : forall c, c < a -> c < b) : a <= b
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
@[simp] lemma iSup_lt_eq_self (a : ℝ≥0∞) : ⨆ b, ⨆ _ : b < a, b = a := by
  refine le_antisymm (iSup₂_le fun b hb ↦ hb.le) ?_
  refine le_of_forall_lt fun c hca ↦ ?_
  obtain ⟨d, hcd, hdb⟩ := exists_between hca
  exact hcd.trans_le <| le_iSup₂_of_le d hdb le_rfl

-- TODO: Prove the two one-side versions
/-
**ENNReal.exists_lt_add_of_lt_add** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：exists_lt_add_of_lt_add {x y z : Real>=0∞} (h : x < y + z) (hy : y != 0) (
hz : z != 0) : exists y' < y, exists z' < z, x < y' + z'
参数：h : x < y + z；hy : y != 0；hz : z != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ENNReal.iSup_lt_eq_self`：∀ (a : ENNReal), ⨆ b, ⨆ (_ : b < a), b = a
· 使用引理 `ENNReal.biSup_add_biSup_le'`：biSup_add_biSup_le' {p : ι -> Prop} {q : κ 
-> Prop} (hp : exists i, p i) (hq : exists j, q j) {g : κ -> Real>=0∞} (h : fora
ll i, p i -> fora…
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
-/
lemma exists_lt_add_of_lt_add {x y z : ℝ≥0∞} (h : x < y + z) (hy : y ≠ 0) (hz : z ≠ 0) :
    ∃ y' < y, ∃ z' < z, x < y' + z' := by
  contrapose! h
  simpa using biSup_add_biSup_le' (by exact ⟨0, hy.bot_lt⟩) (by exact ⟨0, hz.bot_lt⟩) h

end iSup

end ENNReal

