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

variable {a b c d : Real>=0∞} {r p q : Real>=0}

section Mul

@[mono, gcongr]
/--
theorem `mul_lt_mul` / 定理 `mul_lt_mul`

English:
theorem mul_lt_mul
  given: (ac : a < c) (bd : b < d)
  statement: a * b < c * d
  proof: WithTop.mul_lt_mul ac bd

中文:
定理 mul_lt_mul
  条件: (ac : a < c) (bd : b < d)
  结论: a * b < c * d
  证明: WithTop.mul_lt_mul ac bd

Depends on / 依赖: WithTop, WithTop.mul_lt_mul, mul_lt_mul
-/
theorem mul_lt_mul (ac : a < c) (bd : b < d) : a * b < c * d := WithTop.mul_lt_mul ac bd

/--
lemma `pow_right_strictMono` / 引理 `pow_right_strictMono`

English:
lemma pow_right_strictMono
  given: {n : Nat} (hn : n != 0)
  statement: StrictMono fun a : Real>=0∞ => a ^ n
  proof: WithTop.pow_right_strictMono hn

中文:
引理 pow_right_strictMono
  条件: {n : 自然数} (hn : n != 0)
  结论: StrictMono fun a : 实数>=0∞ => a ^ n
  证明: WithTop.pow_right_strictMono hn
-/
protected lemma pow_right_strictMono {n : Nat} (hn : n != 0) : StrictMono fun a : Real>=0∞ => a ^ n :=
  WithTop.pow_right_strictMono hn

/--
lemma `pow_le_pow_left_iff` / 引理 `pow_le_pow_left_iff`

English:
lemma pow_le_pow_left_iff
  given: {n : Nat} (hn : n != 0)
  statement: a ^ n <= b ^ n ↔ a <= b
  proof: (ENNReal.pow_right_strictMono hn).le_iff_le

中文:
引理 pow_le_pow_left_iff
  条件: {n : 自然数} (hn : n != 0)
  结论: a ^ n <= b ^ n ↔ a <= b
  证明: (ENNReal.pow_right_strictMono hn).le_iff_le
-/
protected lemma pow_le_pow_left_iff {n : Nat} (hn : n != 0) : a ^ n <= b ^ n ↔ a <= b :=
  (ENNReal.pow_right_strictMono hn).le_iff_le

/--
lemma `pow_lt_pow_left_iff` / 引理 `pow_lt_pow_left_iff`

English:
lemma pow_lt_pow_left_iff
  given: {n : Nat} (hn : n != 0)
  statement: a ^ n < b ^ n ↔ a < b
  proof: (ENNReal.pow_right_strictMono hn).lt_iff_lt

中文:
引理 pow_lt_pow_left_iff
  条件: {n : 自然数} (hn : n != 0)
  结论: a ^ n < b ^ n ↔ a < b
  证明: (ENNReal.pow_right_strictMono hn).lt_iff_lt
-/
protected lemma pow_lt_pow_left_iff {n : Nat} (hn : n != 0) : a ^ n < b ^ n ↔ a < b :=
  (ENNReal.pow_right_strictMono hn).lt_iff_lt

/--
lemma `pow_le_pow_left` / 引理 `pow_le_pow_left`

English:
lemma pow_le_pow_left
  given: {n : Nat} (h : a <= b)
  statement: a ^ n <= b ^ n
  proof: pow_le_pow_left' h n
@[mono, gcongr] protected alias ⟨_, pow_lt_pow_left⟩ := ENNReal.pow_lt_pow_left_iff

中文:
引理 pow_le_pow_left
  条件: {n : 自然数} (h : a <= b)
  结论: a ^ n <= b ^ n
  证明: pow_le_pow_left' h n
@[mono, gcongr] protected alias ⟨_, pow_lt_pow_left⟩ := ENNReal.pow_lt_pow_left_iff
-/
@[mono, gcongr] protected lemma pow_le_pow_left {n : Nat} (h : a <= b) : a ^ n <= b ^ n :=
  pow_le_pow_left' h n
@[mono, gcongr] protected alias ⟨_, pow_lt_pow_left⟩ := ENNReal.pow_lt_pow_left_iff

/--
lemma `mul_left_strictMono` / 引理 `mul_left_strictMono`

English:
lemma mul_left_strictMono
  given: (h₀ : a != 0) (hinf : a != ∞)
  statement: StrictMono (· * a)
  proof: WithTop.mul_left_strictMono (pos_iff_ne_zero.2 h₀) hinf

中文:
引理 mul_left_strictMono
  条件: (h₀ : a != 0) (hinf : a != ∞)
  结论: StrictMono (· * a)
  证明: WithTop.mul_left_strictMono (pos_iff_ne_zero.2 h₀) hinf

Depends on / 依赖: WithTop, WithTop.mul_left_strictMono, mul_left_strictMono, pos_iff_ne_zero
-/
lemma mul_left_strictMono (h₀ : a != 0) (hinf : a != ∞) : StrictMono (· * a) :=
  WithTop.mul_left_strictMono (pos_iff_ne_zero.2 h₀) hinf

/--
lemma `mul_right_strictMono` / 引理 `mul_right_strictMono`

English:
lemma mul_right_strictMono
  given: (h₀ : a != 0) (hinf : a != ∞)
  statement: StrictMono (a * ·)
  proof: WithTop.mul_right_strictMono (pos_iff_ne_zero.2 h₀) hinf

中文:
引理 mul_right_strictMono
  条件: (h₀ : a != 0) (hinf : a != ∞)
  结论: StrictMono (a * ·)
  证明: WithTop.mul_right_strictMono (pos_iff_ne_zero.2 h₀) hinf

Depends on / 依赖: WithTop, WithTop.mul_right_strictMono, mul_right_strictMono, pos_iff_ne_zero
-/
lemma mul_right_strictMono (h₀ : a != 0) (hinf : a != ∞) : StrictMono (a * ·) :=
  WithTop.mul_right_strictMono (pos_iff_ne_zero.2 h₀) hinf

/--
theorem `mul_lt_mul_right` / 定理 `mul_lt_mul_right`

English:
theorem mul_lt_mul_right
  given: (h0 : a != 0) (hinf : a != ⊤) (bc : b < c)
  proof: ENNReal.mul_right_strictMono h0 hinf bc

中文:
定理 mul_lt_mul_right
  条件: (h0 : a != 0) (hinf : a != ⊤) (bc : b < c)
  证明: ENNReal.mul_right_strictMono h0 hinf bc
-/
@[gcongr] protected theorem mul_lt_mul_right (h0 : a != 0) (hinf : a != ⊤) (bc : b < c) :
    a * b < a * c :=
  ENNReal.mul_right_strictMono h0 hinf bc

/--
theorem `mul_lt_mul_left` / 定理 `mul_lt_mul_left`

English:
theorem mul_lt_mul_left
  given: (h0 : a != 0) (hinf : a != ⊤) (bc : b < c)
  proof: mul_comm b a ▸ mul_comm c a ▸ ENNReal.mul_right_strictMono h0 hinf bc

中文:
定理 mul_lt_mul_left
  条件: (h0 : a != 0) (hinf : a != ⊤) (bc : b < c)
  证明: mul_comm b a ▸ mul_comm c a ▸ ENNReal.mul_right_strictMono h0 hinf bc
-/
@[gcongr] protected theorem mul_lt_mul_left (h0 : a != 0) (hinf : a != ⊤) (bc : b < c) :
    b * a < c * a :=
  mul_comm b a ▸ mul_comm c a ▸ ENNReal.mul_right_strictMono h0 hinf bc

-- TODO: generalize to `WithTop`
/--
theorem `mul_right_inj` / 定理 `mul_right_inj`

English:
theorem mul_right_inj
  given: (h0 : a != 0) (hinf : a != ∞)
  statement: a * b = a * c ↔ b = c
  proof: (mul_right_strictMono h0 hinf).injective.eq_iff

中文:
定理 mul_right_inj
  条件: (h0 : a != 0) (hinf : a != ∞)
  结论: a * b = a * c ↔ b = c
  证明: (mul_right_strictMono h0 hinf).injective.eq_iff
-/
protected theorem mul_right_inj (h0 : a != 0) (hinf : a != ∞) : a * b = a * c ↔ b = c :=
  (mul_right_strictMono h0 hinf).injective.eq_iff

-- TODO: generalize to `WithTop`
/--
theorem `mul_left_inj` / 定理 `mul_left_inj`

English:
theorem mul_left_inj
  given: (h0 : c != 0) (hinf : c != ∞)
  statement: a * c = b * c ↔ a = b
  proof: mul_comm c a ▸ mul_comm c b ▸ ENNReal.mul_right_inj h0 hinf

中文:
定理 mul_left_inj
  条件: (h0 : c != 0) (hinf : c != ∞)
  结论: a * c = b * c ↔ a = b
  证明: mul_comm c a ▸ mul_comm c b ▸ ENNReal.mul_right_inj h0 hinf
-/
protected theorem mul_left_inj (h0 : c != 0) (hinf : c != ∞) : a * c = b * c ↔ a = b :=
  mul_comm c a ▸ mul_comm c b ▸ ENNReal.mul_right_inj h0 hinf

-- TODO: generalize to `WithTop`
/--
lemma `mul_le_mul_iff_right` / 引理 `mul_le_mul_iff_right`

English:
lemma mul_le_mul_iff_right
  given: (h0 : a != 0) (hinf : a != ∞)
  statement: a * b <= a * c ↔ b <= c
  proof: (mul_right_strictMono h0 hinf).le_iff_le

中文:
引理 mul_le_mul_iff_right
  条件: (h0 : a != 0) (hinf : a != ∞)
  结论: a * b <= a * c ↔ b <= c
  证明: (mul_right_strictMono h0 hinf).le_iff_le
-/
protected lemma mul_le_mul_iff_right (h0 : a != 0) (hinf : a != ∞) : a * b <= a * c ↔ b <= c :=
  (mul_right_strictMono h0 hinf).le_iff_le

-- TODO: generalize to `WithTop`
/--
lemma `mul_le_mul_iff_left` / 引理 `mul_le_mul_iff_left`

English:
lemma mul_le_mul_iff_left
  given: (h0 : c != 0) (hinf : c != ∞)
  statement: a * c <= b * c ↔ a <= b
  proof: (mul_left_strictMono h0 hinf).le_iff_le

中文:
引理 mul_le_mul_iff_left
  条件: (h0 : c != 0) (hinf : c != ∞)
  结论: a * c <= b * c ↔ a <= b
  证明: (mul_left_strictMono h0 hinf).le_iff_le
-/
protected lemma mul_le_mul_iff_left (h0 : c != 0) (hinf : c != ∞) : a * c <= b * c ↔ a <= b :=
  (mul_left_strictMono h0 hinf).le_iff_le

-- TODO: generalize to `WithTop`
/--
lemma `mul_lt_mul_iff_right` / 引理 `mul_lt_mul_iff_right`

English:
lemma mul_lt_mul_iff_right
  given: (h0 : a != 0) (hinf : a != ∞)
  statement: a * b < a * c ↔ b < c
  proof: (mul_right_strictMono h0 hinf).lt_iff_lt

中文:
引理 mul_lt_mul_iff_right
  条件: (h0 : a != 0) (hinf : a != ∞)
  结论: a * b < a * c ↔ b < c
  证明: (mul_right_strictMono h0 hinf).lt_iff_lt
-/
protected lemma mul_lt_mul_iff_right (h0 : a != 0) (hinf : a != ∞) : a * b < a * c ↔ b < c :=
  (mul_right_strictMono h0 hinf).lt_iff_lt

-- TODO: generalize to `WithTop`
/--
lemma `mul_lt_mul_iff_left` / 引理 `mul_lt_mul_iff_left`

English:
lemma mul_lt_mul_iff_left
  given: (h0 : c != 0) (hinf : c != ∞)
  statement: a * c < b * c ↔ a < b
  proof: (mul_left_strictMono h0 hinf).lt_iff_lt

中文:
引理 mul_lt_mul_iff_left
  条件: (h0 : c != 0) (hinf : c != ∞)
  结论: a * c < b * c ↔ a < b
  证明: (mul_left_strictMono h0 hinf).lt_iff_lt
-/
protected lemma mul_lt_mul_iff_left (h0 : c != 0) (hinf : c != ∞) : a * c < b * c ↔ a < b :=
  (mul_left_strictMono h0 hinf).lt_iff_lt

/--
lemma `mul_eq_left` / 引理 `mul_eq_left`

English:
lemma mul_eq_left
  given: (ha₀ : a != 0) (ha : a != ∞)
  statement: a * b = a ↔ b = 1
  proof: by
  simpa using ENNReal.mul_right_inj ha₀ ha (c := 1)

中文:
引理 mul_eq_left
  条件: (ha₀ : a != 0) (ha : a != ∞)
  结论: a * b = a ↔ b = 1
  证明: by
  simpa using ENNReal.mul_right_inj ha₀ ha (c := 1)
-/
protected lemma mul_eq_left (ha₀ : a != 0) (ha : a != ∞) : a * b = a ↔ b = 1 := by
  simpa using ENNReal.mul_right_inj ha₀ ha (c := 1)

/--
lemma `mul_eq_right` / 引理 `mul_eq_right`

English:
lemma mul_eq_right
  given: (hb₀ : b != 0) (hb : b != ∞)
  statement: a * b = b ↔ a = 1
  proof: by
  simpa using ENNReal.mul_left_inj hb₀ hb (b := 1)

中文:
引理 mul_eq_right
  条件: (hb₀ : b != 0) (hb : b != ∞)
  结论: a * b = b ↔ a = 1
  证明: by
  simpa using ENNReal.mul_left_inj hb₀ hb (b := 1)
-/
protected lemma mul_eq_right (hb₀ : b != 0) (hb : b != ∞) : a * b = b ↔ a = 1 := by
  simpa using ENNReal.mul_left_inj hb₀ hb (b := 1)

end Mul

section OperationsAndOrder

/--
theorem `pow_pos` / 定理 `pow_pos`

English:
theorem pow_pos
  statement: 0 < a -> forall n : Nat, 0 < a ^ n
  proof: CanonicallyOrderedAdd.pow_pos

中文:
定理 pow_pos
  结论: 0 < a -> 对任意 n : 自然数, 0 < a ^ n
  证明: CanonicallyOrderedAdd.pow_pos
-/
protected theorem pow_pos : 0 < a -> forall n : Nat, 0 < a ^ n :=
  CanonicallyOrderedAdd.pow_pos

/--
theorem `pow_ne_zero` / 定理 `pow_ne_zero`

English:
theorem pow_ne_zero
  statement: a != 0 -> forall n : Nat, a ^ n != 0
  proof: by
  simpa only [pos_iff_ne_zero] using ENNReal.pow_pos

中文:
定理 pow_ne_zero
  结论: a != 0 -> 对任意 n : 自然数, a ^ n != 0
  证明: by
  simpa only [pos_iff_ne_zero] using ENNReal.pow_pos
-/
protected theorem pow_ne_zero : a != 0 -> forall n : Nat, a ^ n != 0 := by
  simpa only [pos_iff_ne_zero] using ENNReal.pow_pos

/--
theorem `not_lt_zero` / 定理 `not_lt_zero`

English:
theorem not_lt_zero
  statement: ¬a < 0
  proof: by simp

中文:
定理 not_lt_zero
  结论: ¬a < 0
  证明: by simp
-/
theorem not_lt_zero : ¬a < 0 := by simp

/--
theorem `le_of_add_le_add_left` / 定理 `le_of_add_le_add_left`

English:
theorem le_of_add_le_add_left
  statement: a != ∞ -> a + b <= a + c -> b <= c
  proof: WithTop.le_of_add_le_add_left

中文:
定理 le_of_add_le_add_left
  结论: a != ∞ -> a + b <= a + c -> b <= c
  证明: WithTop.le_of_add_le_add_left
-/
protected theorem le_of_add_le_add_left : a != ∞ -> a + b <= a + c -> b <= c :=
  WithTop.le_of_add_le_add_left

/--
theorem `le_of_add_le_add_right` / 定理 `le_of_add_le_add_right`

English:
theorem le_of_add_le_add_right
  statement: a != ∞ -> b + a <= c + a -> b <= c
  proof: WithTop.le_of_add_le_add_right

中文:
定理 le_of_add_le_add_right
  结论: a != ∞ -> b + a <= c + a -> b <= c
  证明: WithTop.le_of_add_le_add_right
-/
protected theorem le_of_add_le_add_right : a != ∞ -> b + a <= c + a -> b <= c :=
  WithTop.le_of_add_le_add_right

/--
theorem `add_lt_add_left` / 定理 `add_lt_add_left`

English:
theorem add_lt_add_left
  statement: a != ∞ -> b < c -> a + b < a + c
  proof: WithTop.add_lt_add_left

中文:
定理 add_lt_add_left
  结论: a != ∞ -> b < c -> a + b < a + c
  证明: WithTop.add_lt_add_left
-/
@[gcongr] protected theorem add_lt_add_left : a != ∞ -> b < c -> a + b < a + c :=
  WithTop.add_lt_add_left

/--
theorem `add_lt_add_right` / 定理 `add_lt_add_right`

English:
theorem add_lt_add_right
  statement: a != ∞ -> b < c -> b + a < c + a
  proof: WithTop.add_lt_add_right

中文:
定理 add_lt_add_right
  结论: a != ∞ -> b < c -> b + a < c + a
  证明: WithTop.add_lt_add_right
-/
@[gcongr] protected theorem add_lt_add_right : a != ∞ -> b < c -> b + a < c + a :=
  WithTop.add_lt_add_right

/--
theorem `add_le_add_iff_left` / 定理 `add_le_add_iff_left`

English:
theorem add_le_add_iff_left
  statement: a != ∞ -> (a + b <= a + c ↔ b <= c)
  proof: WithTop.add_le_add_iff_left

中文:
定理 add_le_add_iff_left
  结论: a != ∞ -> (a + b <= a + c ↔ b <= c)
  证明: WithTop.add_le_add_iff_left
-/
protected theorem add_le_add_iff_left : a != ∞ -> (a + b <= a + c ↔ b <= c) :=
  WithTop.add_le_add_iff_left

/--
theorem `add_le_add_iff_right` / 定理 `add_le_add_iff_right`

English:
theorem add_le_add_iff_right
  statement: a != ∞ -> (b + a <= c + a ↔ b <= c)
  proof: WithTop.add_le_add_iff_right

中文:
定理 add_le_add_iff_right
  结论: a != ∞ -> (b + a <= c + a ↔ b <= c)
  证明: WithTop.add_le_add_iff_right
-/
protected theorem add_le_add_iff_right : a != ∞ -> (b + a <= c + a ↔ b <= c) :=
  WithTop.add_le_add_iff_right

/--
theorem `add_lt_add_iff_left` / 定理 `add_lt_add_iff_left`

English:
theorem add_lt_add_iff_left
  statement: a != ∞ -> (a + b < a + c ↔ b < c)
  proof: WithTop.add_lt_add_iff_left

中文:
定理 add_lt_add_iff_left
  结论: a != ∞ -> (a + b < a + c ↔ b < c)
  证明: WithTop.add_lt_add_iff_left
-/
protected theorem add_lt_add_iff_left : a != ∞ -> (a + b < a + c ↔ b < c) :=
  WithTop.add_lt_add_iff_left

/--
theorem `add_lt_add_iff_right` / 定理 `add_lt_add_iff_right`

English:
theorem add_lt_add_iff_right
  statement: a != ∞ -> (b + a < c + a ↔ b < c)
  proof: WithTop.add_lt_add_iff_right

中文:
定理 add_lt_add_iff_right
  结论: a != ∞ -> (b + a < c + a ↔ b < c)
  证明: WithTop.add_lt_add_iff_right
-/
protected theorem add_lt_add_iff_right : a != ∞ -> (b + a < c + a ↔ b < c) :=
  WithTop.add_lt_add_iff_right

/--
theorem `add_lt_add_of_le_of_lt` / 定理 `add_lt_add_of_le_of_lt`

English:
theorem add_lt_add_of_le_of_lt
  statement: a != ∞ -> a <= b -> c < d -> a + c < b + d
  proof: WithTop.add_lt_add_of_le_of_lt

中文:
定理 add_lt_add_of_le_of_lt
  结论: a != ∞ -> a <= b -> c < d -> a + c < b + d
  证明: WithTop.add_lt_add_of_le_of_lt
-/
protected theorem add_lt_add_of_le_of_lt : a != ∞ -> a <= b -> c < d -> a + c < b + d :=
  WithTop.add_lt_add_of_le_of_lt

/--
theorem `add_lt_add_of_lt_of_le` / 定理 `add_lt_add_of_lt_of_le`

English:
theorem add_lt_add_of_lt_of_le
  statement: c != ∞ -> a < b -> c <= d -> a + c < b + d
  proof: WithTop.add_lt_add_of_lt_of_le

中文:
定理 add_lt_add_of_lt_of_le
  结论: c != ∞ -> a < b -> c <= d -> a + c < b + d
  证明: WithTop.add_lt_add_of_lt_of_le
-/
protected theorem add_lt_add_of_lt_of_le : c != ∞ -> a < b -> c <= d -> a + c < b + d :=
  WithTop.add_lt_add_of_lt_of_le

/--
Instance `addLeftReflectLT` / 实例 `addLeftReflectLT`

English:
instance addLeftReflectLT
  signature: : AddLeftReflectLT Real>=0∞
  body: WithTop.addLeftReflectLT

中文:
实例 addLeftReflectLT
  签名: : AddLeftReflectLT 实数>=0∞
  定义体: WithTop.addLeftReflectLT

Depends on / 依赖: WithTop, WithTop.addLeftReflectLT, addLeftReflectLT
-/
instance addLeftReflectLT : AddLeftReflectLT Real>=0∞ :=
  WithTop.addLeftReflectLT

/--
theorem `lt_add_right` / 定理 `lt_add_right`

English:
theorem lt_add_right
  given: (ha : a != ∞) (hb : b != 0)
  statement: a < a + b
  proof: by
  rwa [← pos_iff_ne_zero, ← ENNReal.add_lt_add_iff_left ha, add_zero] at hb

中文:
定理 lt_add_right
  条件: (ha : a != ∞) (hb : b != 0)
  结论: a < a + b
  证明: by
  rwa [← pos_iff_ne_zero, ← ENNReal.add_lt_add_iff_left ha, add_zero] at hb

Depends on / 依赖: ENNReal, ENNReal.add_lt_add_iff_left, add_lt_add_iff_left, add_zero, pos_iff_ne_zero
-/
theorem lt_add_right (ha : a != ∞) (hb : b != 0) : a < a + b := by
  rwa [← pos_iff_ne_zero, ← ENNReal.add_lt_add_iff_left ha, add_zero] at hb

end OperationsAndOrder

section OperationsAndInfty

variable {α : Type*} {n : Nat}

/--
theorem `add_eq_top` / 定理 `add_eq_top`

English:
theorem add_eq_top
  statement: a + b = ∞ ↔ a = ∞ ∨ b = ∞
  proof: WithTop.add_eq_top

中文:
定理 add_eq_top
  结论: a + b = ∞ ↔ a = ∞ ∨ b = ∞
  证明: WithTop.add_eq_top
-/
@[simp] theorem add_eq_top : a + b = ∞ ↔ a = ∞ ∨ b = ∞ := WithTop.add_eq_top

/--
theorem `add_lt_top` / 定理 `add_lt_top`

English:
theorem add_lt_top
  statement: a + b < ∞ ↔ a < ∞ ∧ b < ∞
  proof: WithTop.add_lt_top

中文:
定理 add_lt_top
  结论: a + b < ∞ ↔ a < ∞ ∧ b < ∞
  证明: WithTop.add_lt_top
-/
@[simp] theorem add_lt_top : a + b < ∞ ↔ a < ∞ ∧ b < ∞ := WithTop.add_lt_top

/--
theorem `toNNReal_add` / 定理 `toNNReal_add`

English:
theorem toNNReal_add
  given: {r₁ r₂ : Real>=0∞} (h₁ : r₁ != ∞) (h₂ : r₂ != ∞)
  proof: by
  lift r₁ to Real>=0 using h₁
  lift r₂ to Real>=0 using h₂
  rfl

中文:
定理 toNNReal_add
  条件: {r₁ r₂ : 实数>=0∞} (h₁ : r₁ != ∞) (h₂ : r₂ != ∞)
  证明: by
  lift r₁ to Real>=0 using h₁
  lift r₂ to Real>=0 using h₂
  rfl
-/
theorem toNNReal_add {r₁ r₂ : Real>=0∞} (h₁ : r₁ != ∞) (h₂ : r₂ != ∞) :
    (r₁ + r₂).toNNReal = r₁.toNNReal + r₂.toNNReal := by
  lift r₁ to Real>=0 using h₁
  lift r₂ to Real>=0 using h₂
  rfl

/--
theorem `toReal_le_add'` / 定理 `toReal_le_add'`

English:
theorem toReal_le_add'
  given: (hle : a <= b + c) (hb : b = ∞ -> a = ∞) (hc : c = ∞ -> a = ∞)
  proof: by
  refine le_trans (toReal_mono' hle ?_) toReal_add_le
  simpa only [add_eq_top, or_imp] using And.intro hb hc

中文:
定理 toReal_le_add'
  条件: (hle : a <= b + c) (hb : b = ∞ -> a = ∞) (hc : c = ∞ -> a = ∞)
  证明: by
  refine le_trans (toReal_mono' hle ?_) toReal_add_le
  simpa only [add_eq_top, or_imp] using And.intro hb hc

Depends on / 依赖: And.intro, add_eq_top, le_trans, or_imp, toReal_add_le, toReal_mono
-/
theorem toReal_le_add' (hle : a <= b + c) (hb : b = ∞ -> a = ∞) (hc : c = ∞ -> a = ∞) :
    a.toReal <= b.toReal + c.toReal := by
  refine le_trans (toReal_mono' hle ?_) toReal_add_le
  simpa only [add_eq_top, or_imp] using And.intro hb hc

/--
theorem `toReal_le_add` / 定理 `toReal_le_add`

English:
theorem toReal_le_add
  given: (hle : a <= b + c) (hb : b != ∞) (hc : c != ∞)
  proof: toReal_le_add' hle (flip absurd hb) (flip absurd hc)

中文:
定理 toReal_le_add
  条件: (hle : a <= b + c) (hb : b != ∞) (hc : c != ∞)
  证明: toReal_le_add' hle (flip absurd hb) (flip absurd hc)

Depends on / 依赖: absurd, toReal_le_add
-/
theorem toReal_le_add (hle : a <= b + c) (hb : b != ∞) (hc : c != ∞) :
    a.toReal <= b.toReal + c.toReal :=
  toReal_le_add' hle (flip absurd hb) (flip absurd hc)

/--
theorem `not_lt_top` / 定理 `not_lt_top`

English:
theorem not_lt_top
  given: {x : Real>=0∞}
  statement: ¬x < ∞ ↔ x = ∞
  proof: by rw [lt_top_iff_ne_top, Classical.not_not]

中文:
定理 not_lt_top
  条件: {x : 实数>=0∞}
  结论: ¬x < ∞ ↔ x = ∞
  证明: by rw [lt_top_iff_ne_top, Classical.not_not]

Depends on / 依赖: Classical, Classical.not_not, lt_top_iff_ne_top, not_not
-/
theorem not_lt_top {x : Real>=0∞} : ¬x < ∞ ↔ x = ∞ := by rw [lt_top_iff_ne_top, Classical.not_not]

/--
theorem `add_ne_top` / 定理 `add_ne_top`

English:
theorem add_ne_top
  statement: a + b != ∞ ↔ a != ∞ ∧ b != ∞
  proof: by simpa only [lt_top_iff_ne_top] using add_lt_top

@[aesop (rule_sets := [finiteness]) safe apply]

中文:
定理 add_ne_top
  结论: a + b != ∞ ↔ a != ∞ ∧ b != ∞
  证明: by simpa only [lt_top_iff_ne_top] using add_lt_top

@[aesop (rule_sets := [finiteness]) safe apply]

Depends on / 依赖: add_lt_top, lt_top_iff_ne_top
-/
theorem add_ne_top : a + b != ∞ ↔ a != ∞ ∧ b != ∞ := by simpa only [lt_top_iff_ne_top] using add_lt_top

@[aesop (rule_sets := [finiteness]) safe apply]
/--
lemma `Finiteness.add_ne_top` / 引理 `Finiteness.add_ne_top`

English:
lemma Finiteness.add_ne_top
  given: {a b : Real>=0∞} (ha : a != ∞) (hb : b != ∞)
  statement: a + b != ∞
  proof: ENNReal.add_ne_top.2 ⟨ha, hb⟩

中文:
引理 Finiteness.add_ne_top
  条件: {a b : 实数>=0∞} (ha : a != ∞) (hb : b != ∞)
  结论: a + b != ∞
  证明: ENNReal.add_ne_top.2 ⟨ha, hb⟩
-/
protected lemma Finiteness.add_ne_top {a b : Real>=0∞} (ha : a != ∞) (hb : b != ∞) : a + b != ∞ :=
  ENNReal.add_ne_top.2 ⟨ha, hb⟩

/--
theorem `mul_top'` / 定理 `mul_top'`

English:
theorem mul_top'
  statement: a * ∞ = if a = 0 then 0 else ∞
  proof: by convert! WithTop.mul_top' a

中文:
定理 mul_top'
  结论: a * ∞ = if a = 0 then 0 else ∞
  证明: by convert! WithTop.mul_top' a

Depends on / 依赖: WithTop, WithTop.mul_top, convert, mul_top
-/
theorem mul_top' : a * ∞ = if a = 0 then 0 else ∞ := by convert! WithTop.mul_top' a

/--
theorem `mul_top` / 定理 `mul_top`

English:
theorem mul_top
  given: (h : a != 0)
  statement: a * ∞ = ∞
  proof: WithTop.mul_top h

中文:
定理 mul_top
  条件: (h : a != 0)
  结论: a * ∞ = ∞
  证明: WithTop.mul_top h
-/
@[simp] theorem mul_top (h : a != 0) : a * ∞ = ∞ := WithTop.mul_top h

/--
theorem `top_mul'` / 定理 `top_mul'`

English:
theorem top_mul'
  statement: ∞ * a = if a = 0 then 0 else ∞
  proof: by convert! WithTop.top_mul' a

中文:
定理 top_mul'
  结论: ∞ * a = if a = 0 then 0 else ∞
  证明: by convert! WithTop.top_mul' a

Depends on / 依赖: WithTop, WithTop.top_mul, convert, top_mul
-/
theorem top_mul' : ∞ * a = if a = 0 then 0 else ∞ := by convert! WithTop.top_mul' a

/--
theorem `top_mul` / 定理 `top_mul`

English:
theorem top_mul
  given: (h : a != 0)
  statement: ∞ * a = ∞
  proof: WithTop.top_mul h

中文:
定理 top_mul
  条件: (h : a != 0)
  结论: ∞ * a = ∞
  证明: WithTop.top_mul h
-/
@[simp] theorem top_mul (h : a != 0) : ∞ * a = ∞ := WithTop.top_mul h

/--
theorem `top_mul_top` / 定理 `top_mul_top`

English:
theorem top_mul_top
  statement: ∞ * ∞ = ∞
  proof: WithTop.top_mul_top

中文:
定理 top_mul_top
  结论: ∞ * ∞ = ∞
  证明: WithTop.top_mul_top

Depends on / 依赖: WithTop, WithTop.top_mul_top, top_mul_top
-/
theorem top_mul_top : ∞ * ∞ = ∞ := WithTop.top_mul_top

/--
theorem `mul_eq_top` / 定理 `mul_eq_top`

English:
theorem mul_eq_top
  statement: a * b = ∞ ↔ a != 0 ∧ b = ∞ ∨ a = ∞ ∧ b != 0
  proof: WithTop.mul_eq_top_iff

中文:
定理 mul_eq_top
  结论: a * b = ∞ ↔ a != 0 ∧ b = ∞ ∨ a = ∞ ∧ b != 0
  证明: WithTop.mul_eq_top_iff

Depends on / 依赖: WithTop, WithTop.mul_eq_top_iff, mul_eq_top_iff
-/
theorem mul_eq_top : a * b = ∞ ↔ a != 0 ∧ b = ∞ ∨ a = ∞ ∧ b != 0 :=
  WithTop.mul_eq_top_iff

/--
theorem `mul_lt_top` / 定理 `mul_lt_top`

English:
theorem mul_lt_top
  statement: a < ∞ -> b < ∞ -> a * b < ∞
  proof: WithTop.mul_lt_top

中文:
定理 mul_lt_top
  结论: a < ∞ -> b < ∞ -> a * b < ∞
  证明: WithTop.mul_lt_top

Depends on / 依赖: WithTop, WithTop.mul_lt_top, mul_lt_top
-/
theorem mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞ := WithTop.mul_lt_top

-- This is unsafe because we could have `a = ∞` and `b = 0` or vice-versa
@[aesop (rule_sets := [finiteness]) unsafe 75% apply]
/--
theorem `mul_ne_top` / 定理 `mul_ne_top`

English:
theorem mul_ne_top
  statement: a != ∞ -> b != ∞ -> a * b != ∞
  proof: WithTop.mul_ne_top

中文:
定理 mul_ne_top
  结论: a != ∞ -> b != ∞ -> a * b != ∞
  证明: WithTop.mul_ne_top

Depends on / 依赖: WithTop, WithTop.mul_ne_top, mul_ne_top
-/
theorem mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞ := WithTop.mul_ne_top

/--
theorem `lt_top_of_mul_ne_top_left` / 定理 `lt_top_of_mul_ne_top_left`

English:
theorem lt_top_of_mul_ne_top_left
  given: (h : a * b != ∞) (hb : b != 0)
  statement: a < ∞
  proof: lt_top_iff_ne_top.2 fun ha => h mul_eq_top.2 (Or.inr ⟨ha, hb⟩)

中文:
定理 lt_top_of_mul_ne_top_left
  条件: (h : a * b != ∞) (hb : b != 0)
  结论: a < ∞
  证明: lt_top_iff_ne_top.2 fun ha => h mul_eq_top.2 (Or.inr ⟨ha, hb⟩)

Depends on / 依赖: Or.inr, lt_top_iff_ne_top, mul_eq_top
-/
theorem lt_top_of_mul_ne_top_left (h : a * b != ∞) (hb : b != 0) : a < ∞ :=
lt_top_iff_ne_top.2 fun ha => h mul_eq_top.2 (Or.inr ⟨ha, hb⟩)

/--
theorem `lt_top_of_mul_ne_top_right` / 定理 `lt_top_of_mul_ne_top_right`

English:
theorem lt_top_of_mul_ne_top_right
  given: (h : a * b != ∞) (ha : a != 0)
  statement: b < ∞
  proof: lt_top_of_mul_ne_top_left (by rwa [mul_comm]) ha

中文:
定理 lt_top_of_mul_ne_top_right
  条件: (h : a * b != ∞) (ha : a != 0)
  结论: b < ∞
  证明: lt_top_of_mul_ne_top_left (by rwa [mul_comm]) ha

Depends on / 依赖: lt_top_of_mul_ne_top_left, mul_comm
-/
theorem lt_top_of_mul_ne_top_right (h : a * b != ∞) (ha : a != 0) : b < ∞ :=
  lt_top_of_mul_ne_top_left (by rwa [mul_comm]) ha

/--
theorem `mul_lt_top_iff` / 定理 `mul_lt_top_iff`

English:
theorem mul_lt_top_iff
  given: {a b : Real>=0∞}
  statement: a * b < ∞ ↔ a < ∞ ∧ b < ∞ ∨ a = 0 ∨ b = 0
  proof: by
  constructor
  · intro h
    rw [← or_assoc]; rw [or_iff_not_imp_right]; rw [or_iff_not_imp_right]
    intro hb ha
    exact ⟨lt_top_of_mul_ne_top_left h.ne hb, lt_top_of_mul_ne_top_right h.ne ha⟩
  · rintro (⟨ha, hb⟩ | rfl | rfl) <;> [exact mul_lt_top ha hb; simp; simp]

中文:
定理 mul_lt_top_iff
  条件: {a b : 实数>=0∞}
  结论: a * b < ∞ ↔ a < ∞ ∧ b < ∞ ∨ a = 0 ∨ b = 0
  证明: by
  constructor
  · intro h
    rw [← or_assoc]; rw [or_iff_not_imp_right]; rw [or_iff_not_imp_right]
    intro hb ha
    exact ⟨lt_top_of_mul_ne_top_left h.ne hb, lt_top_of_mul_ne_top_right h.ne ha⟩
  · rintro (⟨ha, hb⟩ | rfl | rfl) <;> [exact mul_lt_top ha hb; simp; simp]

Depends on / 依赖: h.ne, lt_top_of_mul_ne_top_left, lt_top_of_mul_ne_top_right, mul_lt_top, or_assoc, or_iff_not_imp_right
-/
theorem mul_lt_top_iff {a b : Real>=0∞} : a * b < ∞ ↔ a < ∞ ∧ b < ∞ ∨ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    rw [← or_assoc]; rw [or_iff_not_imp_right]; rw [or_iff_not_imp_right]
    intro hb ha
    exact ⟨lt_top_of_mul_ne_top_left h.ne hb, lt_top_of_mul_ne_top_right h.ne ha⟩
  · rintro (⟨ha, hb⟩ | rfl | rfl) <;> [exact mul_lt_top ha hb; simp; simp]

/--
theorem `mul_self_lt_top_iff` / 定理 `mul_self_lt_top_iff`

English:
theorem mul_self_lt_top_iff
  given: {a : Real>=0∞}
  statement: a * a < ⊤ ↔ a < ⊤
  proof: by
  rw [ENNReal.mul_lt_top_iff]; rw [and_self]; rw [or_self]; rw [or_iff_left_iff_imp]
  rintro rfl
  exact zero_lt_top

中文:
定理 mul_self_lt_top_iff
  条件: {a : 实数>=0∞}
  结论: a * a < ⊤ ↔ a < ⊤
  证明: by
  rw [ENNReal.mul_lt_top_iff]; rw [and_self]; rw [or_self]; rw [or_iff_left_iff_imp]
  rintro rfl
  exact zero_lt_top

Depends on / 依赖: ENNReal, ENNReal.mul_lt_top_iff, and_self, mul_lt_top_iff, or_iff_left_iff_imp, or_self, zero_lt_top
-/
theorem mul_self_lt_top_iff {a : Real>=0∞} : a * a < ⊤ ↔ a < ⊤ := by
  rw [ENNReal.mul_lt_top_iff]; rw [and_self]; rw [or_self]; rw [or_iff_left_iff_imp]
  rintro rfl
  exact zero_lt_top

/--
theorem `mul_pos_iff` / 定理 `mul_pos_iff`

English:
theorem mul_pos_iff
  statement: 0 < a * b ↔ 0 < a ∧ 0 < b
  proof: CanonicallyOrderedAdd.mul_pos

中文:
定理 mul_pos_iff
  结论: 0 < a * b ↔ 0 < a ∧ 0 < b
  证明: CanonicallyOrderedAdd.mul_pos

Depends on / 依赖: CanonicallyOrderedAdd, CanonicallyOrderedAdd.mul_pos, mul_pos
-/
theorem mul_pos_iff : 0 < a * b ↔ 0 < a ∧ 0 < b :=
  CanonicallyOrderedAdd.mul_pos

/--
theorem `mul_pos` / 定理 `mul_pos`

English:
theorem mul_pos
  given: (ha : a != 0) (hb : b != 0)
  statement: 0 < a * b
  proof: mul_pos_iff.2 ⟨pos_iff_ne_zero.2 ha, pos_iff_ne_zero.2 hb⟩

中文:
定理 mul_pos
  条件: (ha : a != 0) (hb : b != 0)
  结论: 0 < a * b
  证明: mul_pos_iff.2 ⟨pos_iff_ne_zero.2 ha, pos_iff_ne_zero.2 hb⟩

Depends on / 依赖: mul_pos_iff, pos_iff_ne_zero
-/
theorem mul_pos (ha : a != 0) (hb : b != 0) : 0 < a * b :=
  mul_pos_iff.2 ⟨pos_iff_ne_zero.2 ha, pos_iff_ne_zero.2 hb⟩

/--
lemma `top_pow` / 引理 `top_pow`

English:
lemma top_pow
  given: {n : Nat} (hn : n != 0)
  statement: (∞ : Real>=0∞) ^ n = ∞
  proof: WithTop.top_pow hn

中文:
引理 top_pow
  条件: {n : 自然数} (hn : n != 0)
  结论: (∞ : 实数>=0∞) ^ n = ∞
  证明: WithTop.top_pow hn
-/
@[simp] lemma top_pow {n : Nat} (hn : n != 0) : (∞ : Real>=0∞) ^ n = ∞ := WithTop.top_pow hn

/--
lemma `pow_eq_top_iff` / 引理 `pow_eq_top_iff`

English:
lemma pow_eq_top_iff
  statement: a ^ n = ∞ ↔ a = ∞ ∧ n != 0
  proof: WithTop.pow_eq_top_iff

中文:
引理 pow_eq_top_iff
  结论: a ^ n = ∞ ↔ a = ∞ ∧ n != 0
  证明: WithTop.pow_eq_top_iff
-/
@[simp] lemma pow_eq_top_iff : a ^ n = ∞ ↔ a = ∞ ∧ n != 0 := WithTop.pow_eq_top_iff

/--
lemma `pow_ne_top_iff` / 引理 `pow_ne_top_iff`

English:
lemma pow_ne_top_iff
  statement: a ^ n != ∞ ↔ a != ∞ ∨ n = 0
  proof: WithTop.pow_ne_top_iff

中文:
引理 pow_ne_top_iff
  结论: a ^ n != ∞ ↔ a != ∞ ∨ n = 0
  证明: WithTop.pow_ne_top_iff

Depends on / 依赖: WithTop, WithTop.pow_ne_top_iff, pow_ne_top_iff
-/
lemma pow_ne_top_iff : a ^ n != ∞ ↔ a != ∞ ∨ n = 0 := WithTop.pow_ne_top_iff

/--
lemma `pow_lt_top_iff` / 引理 `pow_lt_top_iff`

English:
lemma pow_lt_top_iff
  statement: a ^ n < ∞ ↔ a < ∞ ∨ n = 0
  proof: WithTop.pow_lt_top_iff

中文:
引理 pow_lt_top_iff
  结论: a ^ n < ∞ ↔ a < ∞ ∨ n = 0
  证明: WithTop.pow_lt_top_iff
-/
@[simp] lemma pow_lt_top_iff : a ^ n < ∞ ↔ a < ∞ ∨ n = 0 := WithTop.pow_lt_top_iff

/--
lemma `eq_top_of_pow` / 引理 `eq_top_of_pow`

English:
lemma eq_top_of_pow
  given: (n : Nat) (ha : a ^ n = ∞)
  statement: a = ∞
  proof: WithTop.eq_top_of_pow n ha

@[aesop (rule_sets := [finiteness]) safe apply]

中文:
引理 eq_top_of_pow
  条件: (n : 自然数) (ha : a ^ n = ∞)
  结论: a = ∞
  证明: WithTop.eq_top_of_pow n ha

@[aesop (rule_sets := [finiteness]) safe apply]

Depends on / 依赖: WithTop, WithTop.eq_top_of_pow, eq_top_of_pow
-/
lemma eq_top_of_pow (n : Nat) (ha : a ^ n = ∞) : a = ∞ := WithTop.eq_top_of_pow n ha

@[aesop (rule_sets := [finiteness]) safe apply]
/--
lemma `pow_ne_top` / 引理 `pow_ne_top`

English:
lemma pow_ne_top
  given: (ha : a != ∞)
  statement: a ^ n != ∞
  proof: WithTop.pow_ne_top ha

中文:
引理 pow_ne_top
  条件: (ha : a != ∞)
  结论: a ^ n != ∞
  证明: WithTop.pow_ne_top ha

Depends on / 依赖: WithTop, WithTop.pow_ne_top, pow_ne_top
-/
lemma pow_ne_top (ha : a != ∞) : a ^ n != ∞ := WithTop.pow_ne_top ha
/--
lemma `pow_lt_top` / 引理 `pow_lt_top`

English:
lemma pow_lt_top
  given: (ha : a < ∞)
  statement: a ^ n < ∞
  proof: WithTop.pow_lt_top ha

中文:
引理 pow_lt_top
  条件: (ha : a < ∞)
  结论: a ^ n < ∞
  证明: WithTop.pow_lt_top ha

Depends on / 依赖: WithTop, WithTop.pow_lt_top, pow_lt_top
-/
lemma pow_lt_top (ha : a < ∞) : a ^ n < ∞ := WithTop.pow_lt_top ha

end OperationsAndInfty

/--
theorem `add_lt_add` / 定理 `add_lt_add`

English:
theorem add_lt_add
  given: (ac : a < c) (bd : b < d)
  statement: a + b < c + d
  proof: WithTop.add_lt_add ac bd

中文:
定理 add_lt_add
  条件: (ac : a < c) (bd : b < d)
  结论: a + b < c + d
  证明: WithTop.add_lt_add ac bd
-/
@[gcongr] protected theorem add_lt_add (ac : a < c) (bd : b < d) : a + b < c + d :=
  WithTop.add_lt_add ac bd

section Cancel

/-- An element `a` is `AddLECancellable` if `a + b ≤ a + c` implies `b ≤ c` for all `b` and `c`.
  This is true in `ℝ≥0∞` for all elements except `∞`. -/
@[simp]
/--
theorem `addLECancellable_iff_ne` / 定理 `addLECancellable_iff_ne`

English:
theorem addLECancellable_iff_ne
  given: {a : Real>=0∞}
  statement: AddLECancellable a ↔ a != ∞
  proof: WithTop.addLECancellable_iff_ne_top

中文:
定理 addLECancellable_iff_ne
  条件: {a : 实数>=0∞}
  结论: AddLECancellable a ↔ a != ∞
  证明: WithTop.addLECancellable_iff_ne_top

Depends on / 依赖: WithTop, WithTop.addLECancellable_iff_ne_top, addLECancellable_iff_ne_top
-/
theorem addLECancellable_iff_ne {a : Real>=0∞} : AddLECancellable a ↔ a != ∞ :=
  WithTop.addLECancellable_iff_ne_top

/--
theorem `cancel_of_ne` / 定理 `cancel_of_ne`

English:
theorem cancel_of_ne
  given: {a : Real>=0∞} (h : a != ∞)
  statement: AddLECancellable a
  proof: addLECancellable_iff_ne.mpr h

中文:
定理 cancel_of_ne
  条件: {a : 实数>=0∞} (h : a != ∞)
  结论: AddLECancellable a
  证明: addLECancellable_iff_ne.mpr h

Depends on / 依赖: addLECancellable_iff_ne, addLECancellable_iff_ne.mpr
-/
theorem cancel_of_ne {a : Real>=0∞} (h : a != ∞) : AddLECancellable a :=
  addLECancellable_iff_ne.mpr h

/--
theorem `cancel_of_lt` / 定理 `cancel_of_lt`

English:
theorem cancel_of_lt
  given: {a : Real>=0∞} (h : a < ∞)
  statement: AddLECancellable a
  proof: cancel_of_ne h.ne

中文:
定理 cancel_of_lt
  条件: {a : 实数>=0∞} (h : a < ∞)
  结论: AddLECancellable a
  证明: cancel_of_ne h.ne

Depends on / 依赖: cancel_of_ne, h.ne
-/
theorem cancel_of_lt {a : Real>=0∞} (h : a < ∞) : AddLECancellable a :=
  cancel_of_ne h.ne

/--
theorem `cancel_of_lt'` / 定理 `cancel_of_lt'`

English:
theorem cancel_of_lt'
  given: {a b : Real>=0∞} (h : a < b)
  statement: AddLECancellable a
  proof: cancel_of_ne h.ne_top

中文:
定理 cancel_of_lt'
  条件: {a b : 实数>=0∞} (h : a < b)
  结论: AddLECancellable a
  证明: cancel_of_ne h.ne_top

Depends on / 依赖: cancel_of_ne, h.ne_top, ne_top
-/
theorem cancel_of_lt' {a b : Real>=0∞} (h : a < b) : AddLECancellable a :=
  cancel_of_ne h.ne_top

/--
theorem `cancel_coe` / 定理 `cancel_coe`

English:
theorem cancel_coe
  given: {a : Real>=0}
  statement: AddLECancellable (a : Real>=0∞)
  proof: cancel_of_ne coe_ne_top

中文:
定理 cancel_coe
  条件: {a : 实数>=0}
  结论: AddLECancellable (a : 实数>=0∞)
  证明: cancel_of_ne coe_ne_top

Depends on / 依赖: cancel_of_ne, coe_ne_top
-/
theorem cancel_coe {a : Real>=0} : AddLECancellable (a : Real>=0∞) :=
  cancel_of_ne coe_ne_top

/--
theorem `add_right_inj` / 定理 `add_right_inj`

English:
theorem add_right_inj
  given: (h : a != ∞)
  statement: a + b = a + c ↔ b = c
  proof: (cancel_of_ne h).inj

中文:
定理 add_right_inj
  条件: (h : a != ∞)
  结论: a + b = a + c ↔ b = c
  证明: (cancel_of_ne h).inj

Depends on / 依赖: cancel_of_ne
-/
theorem add_right_inj (h : a != ∞) : a + b = a + c ↔ b = c :=
  (cancel_of_ne h).inj

/--
theorem `add_left_inj` / 定理 `add_left_inj`

English:
theorem add_left_inj
  given: (h : a != ∞)
  statement: b + a = c + a ↔ b = c
  proof: (cancel_of_ne h).inj_left

中文:
定理 add_left_inj
  条件: (h : a != ∞)
  结论: b + a = c + a ↔ b = c
  证明: (cancel_of_ne h).inj_left

Depends on / 依赖: cancel_of_ne, inj_left
-/
theorem add_left_inj (h : a != ∞) : b + a = c + a ↔ b = c :=
  (cancel_of_ne h).inj_left

end Cancel

section Sub

/--
theorem `sub_eq_sInf` / 定理 `sub_eq_sInf`

English:
theorem sub_eq_sInf
  given: {a b : Real>=0∞}
  statement: a - b = sInf { d | a <= d + b }
  proof: le_antisymm (le_sInf fun _ h => tsub_le_iff_right.mpr h) sInf_le mem_ofPred.2 le_tsub_add

中文:
定理 sub_eq_sInf
  条件: {a b : 实数>=0∞}
  结论: a - b = sInf { d | a <= d + b }
  证明: le_antisymm (le_sInf fun _ h => tsub_le_iff_right.mpr h) sInf_le mem_ofPred.2 le_tsub_add

Depends on / 依赖: le_antisymm, le_sInf, le_tsub_add, mem_ofPred, sInf_le, tsub_le_iff_right, tsub_le_iff_right.mpr
-/
theorem sub_eq_sInf {a b : Real>=0∞} : a - b = sInf { d | a <= d + b } :=
le_antisymm (le_sInf fun _ h => tsub_le_iff_right.mpr h) sInf_le mem_ofPred.2 le_tsub_add

/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  statement: (↑(r - p) : Real>=0∞) = ↑r - ↑p
  proof: WithTop.coe_sub

中文:
定理 coe_sub
  结论: (↑(r - p) : 实数>=0∞) = ↑r - ↑p
  证明: WithTop.coe_sub
-/
@[simp, norm_cast] theorem coe_sub : (↑(r - p) : Real>=0∞) = ↑r - ↑p := WithTop.coe_sub

/--
theorem `top_sub_coe` / 定理 `top_sub_coe`

English:
theorem top_sub_coe
  statement: ∞ - ↑r = ∞
  proof: rfl

中文:
定理 top_sub_coe
  结论: ∞ - ↑r = ∞
  证明: rfl
-/
@[simp] theorem top_sub_coe : ∞ - ↑r = ∞ := rfl

/--
lemma `top_sub` / 引理 `top_sub`

English:
lemma top_sub
  given: (ha : a != ∞)
  statement: ∞ - a = ∞
  proof: by lift a to Real>=0 using ha; exact top_sub_coe

中文:
引理 top_sub
  条件: (ha : a != ∞)
  结论: ∞ - a = ∞
  证明: by lift a to Real>=0 using ha; exact top_sub_coe
-/
@[simp] lemma top_sub (ha : a != ∞) : ∞ - a = ∞ := by lift a to Real>=0 using ha; exact top_sub_coe

/--
theorem `sub_top` / 定理 `sub_top`

English:
theorem sub_top
  statement: a - ∞ = 0
  proof: WithTop.sub_top

中文:
定理 sub_top
  结论: a - ∞ = 0
  证明: WithTop.sub_top
-/
@[simp] theorem sub_top : a - ∞ = 0 := WithTop.sub_top

/--
theorem `sub_eq_top_iff` / 定理 `sub_eq_top_iff`

English:
theorem sub_eq_top_iff
  statement: a - b = ∞ ↔ a = ∞ ∧ b != ∞
  proof: WithTop.sub_eq_top_iff

中文:
定理 sub_eq_top_iff
  结论: a - b = ∞ ↔ a = ∞ ∧ b != ∞
  证明: WithTop.sub_eq_top_iff
-/
@[simp] theorem sub_eq_top_iff : a - b = ∞ ↔ a = ∞ ∧ b != ∞ := WithTop.sub_eq_top_iff
/--
lemma `sub_ne_top_iff` / 引理 `sub_ne_top_iff`

English:
lemma sub_ne_top_iff
  statement: a - b != ∞ ↔ a != ∞ ∨ b = ∞
  proof: WithTop.sub_ne_top_iff

中文:
引理 sub_ne_top_iff
  结论: a - b != ∞ ↔ a != ∞ ∨ b = ∞
  证明: WithTop.sub_ne_top_iff

Depends on / 依赖: WithTop, WithTop.sub_ne_top_iff, sub_ne_top_iff
-/
lemma sub_ne_top_iff : a - b != ∞ ↔ a != ∞ ∨ b = ∞ := WithTop.sub_ne_top_iff

-- This is unsafe because we could have `a = b = ∞`
@[aesop (rule_sets := [finiteness]) unsafe 75% apply]
/--
theorem `sub_ne_top` / 定理 `sub_ne_top`

English:
theorem sub_ne_top
  given: (ha : a != ∞)
  statement: a - b != ∞
  proof: mt sub_eq_top_iff.mp mt And.left ha

@[simp, norm_cast]

中文:
定理 sub_ne_top
  条件: (ha : a != ∞)
  结论: a - b != ∞
  证明: mt sub_eq_top_iff.mp mt And.left ha

@[simp, norm_cast]

Depends on / 依赖: And.left, sub_eq_top_iff, sub_eq_top_iff.mp
-/
theorem sub_ne_top (ha : a != ∞) : a - b != ∞ := mt sub_eq_top_iff.mp mt And.left ha

@[simp, norm_cast]
/--
theorem `natCast_sub` / 定理 `natCast_sub`

English:
theorem natCast_sub
  given: (m n : Nat)
  statement: ↑(m - n) = (m - n : Real>=0∞)
  proof: by
  rw [← coe_natCast]; rw [Nat.cast_tsub]; rw [coe_sub]; rw [coe_natCast]; rw [coe_natCast]

中文:
定理 natCast_sub
  条件: (m n : 自然数)
  结论: ↑(m - n) = (m - n : 实数>=0∞)
  证明: by
  rw [← coe_natCast]; rw [Nat.cast_tsub]; rw [coe_sub]; rw [coe_natCast]; rw [coe_natCast]

Depends on / 依赖: Nat.cast_tsub, cast_tsub, coe_natCast, coe_sub
-/
theorem natCast_sub (m n : Nat) : ↑(m - n) = (m - n : Real>=0∞) := by
  rw [← coe_natCast]; rw [Nat.cast_tsub]; rw [coe_sub]; rw [coe_natCast]; rw [coe_natCast]

/--
theorem `sub_eq_of_eq_add` / 定理 `sub_eq_of_eq_add`

English:
theorem sub_eq_of_eq_add
  given: (hb : b != ∞)
  statement: a = c + b -> a - b = c
  proof: (cancel_of_ne hb).tsub_eq_of_eq_add

中文:
定理 sub_eq_of_eq_add
  条件: (hb : b != ∞)
  结论: a = c + b -> a - b = c
  证明: (cancel_of_ne hb).tsub_eq_of_eq_add
-/
protected theorem sub_eq_of_eq_add (hb : b != ∞) : a = c + b -> a - b = c :=
  (cancel_of_ne hb).tsub_eq_of_eq_add

/--
lemma `sub_eq_of_eq_add'` / 引理 `sub_eq_of_eq_add'`

English:
lemma sub_eq_of_eq_add'
  given: (ha : a != ∞)
  statement: a = c + b -> a - b = c
  proof: (cancel_of_ne ha).tsub_eq_of_eq_add'

中文:
引理 sub_eq_of_eq_add'
  条件: (ha : a != ∞)
  结论: a = c + b -> a - b = c
  证明: (cancel_of_ne ha).tsub_eq_of_eq_add'
-/
protected lemma sub_eq_of_eq_add' (ha : a != ∞) : a = c + b -> a - b = c :=
  (cancel_of_ne ha).tsub_eq_of_eq_add'

/--
theorem `eq_sub_of_add_eq` / 定理 `eq_sub_of_add_eq`

English:
theorem eq_sub_of_add_eq
  given: (hc : c != ∞)
  statement: a + c = b -> a = b - c
  proof: (cancel_of_ne hc).eq_tsub_of_add_eq

中文:
定理 eq_sub_of_add_eq
  条件: (hc : c != ∞)
  结论: a + c = b -> a = b - c
  证明: (cancel_of_ne hc).eq_tsub_of_add_eq
-/
protected theorem eq_sub_of_add_eq (hc : c != ∞) : a + c = b -> a = b - c :=
  (cancel_of_ne hc).eq_tsub_of_add_eq

/--
lemma `eq_sub_of_add_eq'` / 引理 `eq_sub_of_add_eq'`

English:
lemma eq_sub_of_add_eq'
  given: (hb : b != ∞)
  statement: a + c = b -> a = b - c
  proof: (cancel_of_ne hb).eq_tsub_of_add_eq'

中文:
引理 eq_sub_of_add_eq'
  条件: (hb : b != ∞)
  结论: a + c = b -> a = b - c
  证明: (cancel_of_ne hb).eq_tsub_of_add_eq'
-/
protected lemma eq_sub_of_add_eq' (hb : b != ∞) : a + c = b -> a = b - c :=
  (cancel_of_ne hb).eq_tsub_of_add_eq'

/--
theorem `sub_eq_of_eq_add_rev` / 定理 `sub_eq_of_eq_add_rev`

English:
theorem sub_eq_of_eq_add_rev
  given: (hb : b != ∞)
  statement: a = b + c -> a - b = c
  proof: (cancel_of_ne hb).tsub_eq_of_eq_add_rev

中文:
定理 sub_eq_of_eq_add_rev
  条件: (hb : b != ∞)
  结论: a = b + c -> a - b = c
  证明: (cancel_of_ne hb).tsub_eq_of_eq_add_rev
-/
protected theorem sub_eq_of_eq_add_rev (hb : b != ∞) : a = b + c -> a - b = c :=
  (cancel_of_ne hb).tsub_eq_of_eq_add_rev

/--
lemma `sub_eq_of_eq_add_rev'` / 引理 `sub_eq_of_eq_add_rev'`

English:
lemma sub_eq_of_eq_add_rev'
  given: (ha : a != ∞)
  statement: a = b + c -> a - b = c
  proof: (cancel_of_ne ha).tsub_eq_of_eq_add_rev'

中文:
引理 sub_eq_of_eq_add_rev'
  条件: (ha : a != ∞)
  结论: a = b + c -> a - b = c
  证明: (cancel_of_ne ha).tsub_eq_of_eq_add_rev'
-/
protected lemma sub_eq_of_eq_add_rev' (ha : a != ∞) : a = b + c -> a - b = c :=
  (cancel_of_ne ha).tsub_eq_of_eq_add_rev'

/--
theorem `add_sub_cancel_left` / 定理 `add_sub_cancel_left`

English:
theorem add_sub_cancel_left
  given: (ha : a != ∞)
  statement: a + b - a = b
  proof: by
  simp [ha]

中文:
定理 add_sub_cancel_left
  条件: (ha : a != ∞)
  结论: a + b - a = b
  证明: by
  simp [ha]
-/
protected theorem add_sub_cancel_left (ha : a != ∞) : a + b - a = b := by
  simp [ha]

/--
theorem `add_sub_cancel_right` / 定理 `add_sub_cancel_right`

English:
theorem add_sub_cancel_right
  given: (hb : b != ∞)
  statement: a + b - b = a
  proof: by
  simp [hb]

中文:
定理 add_sub_cancel_right
  条件: (hb : b != ∞)
  结论: a + b - b = a
  证明: by
  simp [hb]
-/
protected theorem add_sub_cancel_right (hb : b != ∞) : a + b - b = a := by
  simp [hb]

/--
theorem `sub_add_eq_add_sub` / 定理 `sub_add_eq_add_sub`

English:
theorem sub_add_eq_add_sub
  given: (hab : b <= a) (b_ne_top : b != ∞)
  proof: by
  by_cases c_top : c = ∞
  · simpa [c_top] using! ENNReal.eq_sub_of_add_eq b_ne_top rfl
  refine ENNReal.eq_sub_of_add_eq b_ne_top ?_
  simp only [add_assoc, add_comm c b]
simpa only [← add_assoc] using! (add_left_inj c_top).mpr tsub_add_cancel_of_le hab

中文:
定理 sub_add_eq_add_sub
  条件: (hab : b <= a) (b_ne_top : b != ∞)
  证明: by
  by_cases c_top : c = ∞
  · simpa [c_top] using! ENNReal.eq_sub_of_add_eq b_ne_top rfl
  refine ENNReal.eq_sub_of_add_eq b_ne_top ?_
  simp only [add_assoc, add_comm c b]
simpa only [← add_assoc] using! (add_left_inj c_top).mpr tsub_add_cancel_of_le hab
-/
protected theorem sub_add_eq_add_sub (hab : b <= a) (b_ne_top : b != ∞) :
    a - b + c = a + c - b := by
  by_cases c_top : c = ∞
  · simpa [c_top] using! ENNReal.eq_sub_of_add_eq b_ne_top rfl
  refine ENNReal.eq_sub_of_add_eq b_ne_top ?_
  simp only [add_assoc, add_comm c b]
simpa only [← add_assoc] using! (add_left_inj c_top).mpr tsub_add_cancel_of_le hab

/--
lemma `add_sub_add_eq_sub_right` / 引理 `add_sub_add_eq_sub_right`

English:
lemma add_sub_add_eq_sub_right
  given: (hc : c != ∞ := by finiteness)
  statement: (a + c) - (b + c) = a - b
  proof: by
  lift c to Real>=0 using hc
  cases a <;> cases b
  · simp
  · simp
  · simp
  · norm_cast
    rw [add_tsub_add_eq_tsub_right]

中文:
引理 add_sub_add_eq_sub_right
  条件: (hc : c != ∞ := by finiteness)
  结论: (a + c) - (b + c) = a - b
  证明: by
  lift c to Real>=0 using hc
  cases a <;> cases b
  · simp
  · simp
  · simp
  · norm_cast
    rw [add_tsub_add_eq_tsub_right]

Depends on / 依赖: add_tsub_add_eq_tsub_right, finiteness
-/
lemma add_sub_add_eq_sub_right (hc : c != ∞ := by finiteness) : (a + c) - (b + c) = a - b := by
  lift c to Real>=0 using hc
  cases a <;> cases b
  · simp
  · simp
  · simp
  · norm_cast
    rw [add_tsub_add_eq_tsub_right]

/--
lemma `add_sub_add_eq_sub_left` / 引理 `add_sub_add_eq_sub_left`

English:
lemma add_sub_add_eq_sub_left
  given: (hc : c != ∞ := by finiteness)
  statement: (c + a) - (c + b) = a - b
  proof: by
  simp_rw [add_comm c]
  exact ENNReal.add_sub_add_eq_sub_right hc

中文:
引理 add_sub_add_eq_sub_left
  条件: (hc : c != ∞ := by finiteness)
  结论: (c + a) - (c + b) = a - b
  证明: by
  simp_rw [add_comm c]
  exact ENNReal.add_sub_add_eq_sub_right hc

Depends on / 依赖: ENNReal, ENNReal.add_sub_add_eq_sub_right, add_comm, add_sub_add_eq_sub_right, finiteness, simp_rw
-/
lemma add_sub_add_eq_sub_left (hc : c != ∞ := by finiteness) : (c + a) - (c + b) = a - b := by
  simp_rw [add_comm c]
  exact ENNReal.add_sub_add_eq_sub_right hc

/--
theorem `lt_add_of_sub_lt_left` / 定理 `lt_add_of_sub_lt_left`

English:
theorem lt_add_of_sub_lt_left
  given: (h : a != ∞ ∨ b != ∞)
  statement: a - b < c -> a < b + c
  proof: by
  obtain rfl | hb := eq_or_ne b ∞
  · rw [top_add, lt_top_iff_ne_top]
    exact fun _ => h.resolve_right (Classical.not_not.2 rfl)
  · exact (cancel_of_ne hb).lt_add_of_tsub_lt_left

中文:
定理 lt_add_of_sub_lt_left
  条件: (h : a != ∞ ∨ b != ∞)
  结论: a - b < c -> a < b + c
  证明: by
  obtain rfl | hb := eq_or_ne b ∞
  · rw [top_add, lt_top_iff_ne_top]
    exact fun _ => h.resolve_right (Classical.not_not.2 rfl)
  · exact (cancel_of_ne hb).lt_add_of_tsub_lt_left
-/
protected theorem lt_add_of_sub_lt_left (h : a != ∞ ∨ b != ∞) : a - b < c -> a < b + c := by
  obtain rfl | hb := eq_or_ne b ∞
  · rw [top_add, lt_top_iff_ne_top]
    exact fun _ => h.resolve_right (Classical.not_not.2 rfl)
  · exact (cancel_of_ne hb).lt_add_of_tsub_lt_left

/--
theorem `lt_add_of_sub_lt_right` / 定理 `lt_add_of_sub_lt_right`

English:
theorem lt_add_of_sub_lt_right
  given: (h : a != ∞ ∨ c != ∞)
  statement: a - c < b -> a < b + c
  proof: add_comm c b ▸ ENNReal.lt_add_of_sub_lt_left h

中文:
定理 lt_add_of_sub_lt_right
  条件: (h : a != ∞ ∨ c != ∞)
  结论: a - c < b -> a < b + c
  证明: add_comm c b ▸ ENNReal.lt_add_of_sub_lt_left h
-/
protected theorem lt_add_of_sub_lt_right (h : a != ∞ ∨ c != ∞) : a - c < b -> a < b + c :=
  add_comm c b ▸ ENNReal.lt_add_of_sub_lt_left h

/--
theorem `le_sub_of_add_le_left` / 定理 `le_sub_of_add_le_left`

English:
theorem le_sub_of_add_le_left
  given: (ha : a != ∞)
  statement: a + b <= c -> b <= c - a
  proof: (cancel_of_ne ha).le_tsub_of_add_le_left

中文:
定理 le_sub_of_add_le_left
  条件: (ha : a != ∞)
  结论: a + b <= c -> b <= c - a
  证明: (cancel_of_ne ha).le_tsub_of_add_le_left

Depends on / 依赖: cancel_of_ne, le_tsub_of_add_le_left
-/
theorem le_sub_of_add_le_left (ha : a != ∞) : a + b <= c -> b <= c - a :=
  (cancel_of_ne ha).le_tsub_of_add_le_left

/--
theorem `le_sub_of_add_le_right` / 定理 `le_sub_of_add_le_right`

English:
theorem le_sub_of_add_le_right
  given: (hb : b != ∞)
  statement: a + b <= c -> a <= c - b
  proof: (cancel_of_ne hb).le_tsub_of_add_le_right

中文:
定理 le_sub_of_add_le_right
  条件: (hb : b != ∞)
  结论: a + b <= c -> a <= c - b
  证明: (cancel_of_ne hb).le_tsub_of_add_le_right

Depends on / 依赖: cancel_of_ne, le_tsub_of_add_le_right
-/
theorem le_sub_of_add_le_right (hb : b != ∞) : a + b <= c -> a <= c - b :=
  (cancel_of_ne hb).le_tsub_of_add_le_right

/--
theorem `sub_lt_of_lt_add` / 定理 `sub_lt_of_lt_add`

English:
theorem sub_lt_of_lt_add
  given: (hac : c <= a) (h : a < b + c)
  statement: a - c < b
  proof: ((cancel_of_lt' <| hac.trans_lt h).tsub_lt_iff_right hac).mpr h

中文:
定理 sub_lt_of_lt_add
  条件: (hac : c <= a) (h : a < b + c)
  结论: a - c < b
  证明: ((cancel_of_lt' <| hac.trans_lt h).tsub_lt_iff_right hac).mpr h
-/
protected theorem sub_lt_of_lt_add (hac : c <= a) (h : a < b + c) : a - c < b :=
  ((cancel_of_lt' <| hac.trans_lt h).tsub_lt_iff_right hac).mpr h

/--
theorem `sub_lt_iff_lt_right` / 定理 `sub_lt_iff_lt_right`

English:
theorem sub_lt_iff_lt_right
  given: (hb : b != ∞) (hab : b <= a)
  statement: a - b < c ↔ a < c + b
  proof: (cancel_of_ne hb).tsub_lt_iff_right hab

中文:
定理 sub_lt_iff_lt_right
  条件: (hb : b != ∞) (hab : b <= a)
  结论: a - b < c ↔ a < c + b
  证明: (cancel_of_ne hb).tsub_lt_iff_right hab
-/
protected theorem sub_lt_iff_lt_right (hb : b != ∞) (hab : b <= a) : a - b < c ↔ a < c + b :=
  (cancel_of_ne hb).tsub_lt_iff_right hab

/--
theorem `sub_lt_iff_lt_left` / 定理 `sub_lt_iff_lt_left`

English:
theorem sub_lt_iff_lt_left
  given: (hb : b != ∞) (hab : b <= a)
  statement: a - b < c ↔ a < b + c
  proof: (cancel_of_ne hb).tsub_lt_iff_left hab

中文:
定理 sub_lt_iff_lt_left
  条件: (hb : b != ∞) (hab : b <= a)
  结论: a - b < c ↔ a < b + c
  证明: (cancel_of_ne hb).tsub_lt_iff_left hab
-/
protected theorem sub_lt_iff_lt_left (hb : b != ∞) (hab : b <= a) : a - b < c ↔ a < b + c :=
  (cancel_of_ne hb).tsub_lt_iff_left hab

/--
theorem `le_sub_iff_add_le_left` / 定理 `le_sub_iff_add_le_left`

English:
theorem le_sub_iff_add_le_left
  given: (hc : c != ∞) (hcb : c <= b)
  statement: a <= b - c ↔ c + a <= b
  proof: ⟨fun h => add_le_of_le_tsub_left_of_le hcb h, le_sub_of_add_le_left hc⟩

中文:
定理 le_sub_iff_add_le_left
  条件: (hc : c != ∞) (hcb : c <= b)
  结论: a <= b - c ↔ c + a <= b
  证明: ⟨fun h => add_le_of_le_tsub_left_of_le hcb h, le_sub_of_add_le_left hc⟩

Depends on / 依赖: add_le_of_le_tsub_left_of_le, le_sub_of_add_le_left
-/
theorem le_sub_iff_add_le_left (hc : c != ∞) (hcb : c <= b) : a <= b - c ↔ c + a <= b :=
  ⟨fun h => add_le_of_le_tsub_left_of_le hcb h, le_sub_of_add_le_left hc⟩

/--
theorem `le_sub_iff_add_le_right` / 定理 `le_sub_iff_add_le_right`

English:
theorem le_sub_iff_add_le_right
  given: (hc : c != ∞) (hcb : c <= b)
  statement: a <= b - c ↔ a + c <= b
  proof: ⟨fun h => add_le_of_le_tsub_right_of_le hcb h, le_sub_of_add_le_right hc⟩

中文:
定理 le_sub_iff_add_le_right
  条件: (hc : c != ∞) (hcb : c <= b)
  结论: a <= b - c ↔ a + c <= b
  证明: ⟨fun h => add_le_of_le_tsub_right_of_le hcb h, le_sub_of_add_le_right hc⟩

Depends on / 依赖: add_le_of_le_tsub_right_of_le, le_sub_of_add_le_right
-/
theorem le_sub_iff_add_le_right (hc : c != ∞) (hcb : c <= b) : a <= b - c ↔ a + c <= b :=
  ⟨fun h => add_le_of_le_tsub_right_of_le hcb h, le_sub_of_add_le_right hc⟩

/--
theorem `sub_lt_self` / 定理 `sub_lt_self`

English:
theorem sub_lt_self
  given: (ha : a != ∞) (ha₀ : a != 0) (hb : b != 0)
  statement: a - b < a
  proof: (cancel_of_ne ha).tsub_lt_self (pos_iff_ne_zero.2 ha₀) (pos_iff_ne_zero.2 hb)

中文:
定理 sub_lt_self
  条件: (ha : a != ∞) (ha₀ : a != 0) (hb : b != 0)
  结论: a - b < a
  证明: (cancel_of_ne ha).tsub_lt_self (pos_iff_ne_zero.2 ha₀) (pos_iff_ne_zero.2 hb)
-/
protected theorem sub_lt_self (ha : a != ∞) (ha₀ : a != 0) (hb : b != 0) : a - b < a :=
  (cancel_of_ne ha).tsub_lt_self (pos_iff_ne_zero.2 ha₀) (pos_iff_ne_zero.2 hb)

/--
theorem `sub_lt_self_iff` / 定理 `sub_lt_self_iff`

English:
theorem sub_lt_self_iff
  given: (ha : a != ∞)
  statement: a - b < a ↔ 0 < a ∧ 0 < b
  proof: (cancel_of_ne ha).tsub_lt_self_iff

中文:
定理 sub_lt_self_iff
  条件: (ha : a != ∞)
  结论: a - b < a ↔ 0 < a ∧ 0 < b
  证明: (cancel_of_ne ha).tsub_lt_self_iff

Depends on / 依赖: Matrix, Matrix.ext
-/
protected theorem sub_lt_self_iff (ha : a != ∞) : a - b < a ↔ 0 < a ∧ 0 < b :=
  (cancel_of_ne ha).tsub_lt_self_iff

/--
theorem `sub_lt_of_sub_lt` / 定理 `sub_lt_of_sub_lt`

English:
theorem sub_lt_of_sub_lt
  given: (h₂ : c <= a) (h₃ : a != ∞ ∨ b != ∞) (h₁ : a - b < c)
  statement: a - c < b
  proof: ENNReal.sub_lt_of_lt_add h₂ (add_comm c b ▸ ENNReal.lt_add_of_sub_lt_right h₃ h₁)

中文:
定理 sub_lt_of_sub_lt
  条件: (h₂ : c <= a) (h₃ : a != ∞ ∨ b != ∞) (h₁ : a - b < c)
  结论: a - c < b
  证明: ENNReal.sub_lt_of_lt_add h₂ (add_comm c b ▸ ENNReal.lt_add_of_sub_lt_right h₃ h₁)

Depends on / 依赖: ENNReal, ENNReal.lt_add_of_sub_lt_right, ENNReal.sub_lt_of_lt_add, add_comm, lt_add_of_sub_lt_right, sub_lt_of_lt_add
-/
theorem sub_lt_of_sub_lt (h₂ : c <= a) (h₃ : a != ∞ ∨ b != ∞) (h₁ : a - b < c) : a - c < b :=
  ENNReal.sub_lt_of_lt_add h₂ (add_comm c b ▸ ENNReal.lt_add_of_sub_lt_right h₃ h₁)

/--
theorem `sub_sub_cancel` / 定理 `sub_sub_cancel`

English:
theorem sub_sub_cancel
  given: (h : a != ∞) (h2 : b <= a)
  statement: a - (a - b) = b
  proof: (cancel_of_ne <| sub_ne_top h).tsub_tsub_cancel_of_le h2

中文:
定理 sub_sub_cancel
  条件: (h : a != ∞) (h2 : b <= a)
  结论: a - (a - b) = b
  证明: (cancel_of_ne <| sub_ne_top h).tsub_tsub_cancel_of_le h2

Depends on / 依赖: cancel_of_ne, dif_pos, sub_ne_top, tsub_tsub_cancel_of_le
-/
theorem sub_sub_cancel (h : a != ∞) (h2 : b <= a) : a - (a - b) = b :=
  (cancel_of_ne <| sub_ne_top h).tsub_tsub_cancel_of_le h2

/--
theorem `sub_right_inj` / 定理 `sub_right_inj`

English:
theorem sub_right_inj
  given: {a b c : Real>=0∞} (ha : a != ∞) (hb : b <= a) (hc : c <= a)
  proof: (cancel_of_ne ha).tsub_right_inj (cancel_of_ne <| ne_top_of_le_ne_top ha hb)
    (cancel_of_ne <| ne_top_of_le_ne_top ha hc) hb hc

中文:
定理 sub_right_inj
  条件: {a b c : 实数>=0∞} (ha : a != ∞) (hb : b <= a) (hc : c <= a)
  证明: (cancel_of_ne ha).tsub_right_inj (cancel_of_ne <| ne_top_of_le_ne_top ha hb)
    (cancel_of_ne <| ne_top_of_le_ne_top ha hc) hb hc

Depends on / 依赖: cancel_of_ne, dif_neg, ne_top_of_le_ne_top, tsub_right_inj
-/
theorem sub_right_inj {a b c : Real>=0∞} (ha : a != ∞) (hb : b <= a) (hc : c <= a) :
    a - b = a - c ↔ b = c :=
  (cancel_of_ne ha).tsub_right_inj (cancel_of_ne <| ne_top_of_le_ne_top ha hb)
    (cancel_of_ne <| ne_top_of_le_ne_top ha hc) hb hc

/--
theorem `sub_mul` / 定理 `sub_mul`

English:
theorem sub_mul
  given: (h : 0 < b -> b < a -> c != ∞)
  statement: (a - b) * c = a * c - b * c
  proof: by
  rcases le_or_gt a b with hab | hab; · simp [hab, mul_left_mono hab, tsub_eq_zero_of_le]
  rcases eq_zero_or_pos b with (rfl | hb); · simp
  exact (cancel_of_ne <| mul_ne_top hab.ne_top (h hb hab)).tsub_mul

中文:
定理 sub_mul
  条件: (h : 0 < b -> b < a -> c != ∞)
  结论: (a - b) * c = a * c - b * c
  证明: by
  rcases le_or_gt a b with hab | hab; · simp [hab, mul_left_mono hab, tsub_eq_zero_of_le]
  rcases eq_zero_or_pos b with (rfl | hb); · simp
  exact (cancel_of_ne <| mul_ne_top hab.ne_top (h hb hab)).tsub_mul

Depends on / 依赖: _apply, apply_dite, blockDiagonal, map_apply
-/
protected theorem sub_mul (h : 0 < b -> b < a -> c != ∞) : (a - b) * c = a * c - b * c := by
  rcases le_or_gt a b with hab | hab; · simp [hab, mul_left_mono hab, tsub_eq_zero_of_le]
  rcases eq_zero_or_pos b with (rfl | hb); · simp
  exact (cancel_of_ne <| mul_ne_top hab.ne_top (h hb hab)).tsub_mul

/--
theorem `mul_sub` / 定理 `mul_sub`

English:
theorem mul_sub
  given: (h : 0 < c -> c < b -> a != ∞)
  statement: a * (b - c) = a * b - a * c
  proof: by
  simp only [mul_comm a]
  exact ENNReal.sub_mul h

中文:
定理 mul_sub
  条件: (h : 0 < c -> c < b -> a != ∞)
  结论: a * (b - c) = a * b - a * c
  证明: by
  simp only [mul_comm a]
  exact ENNReal.sub_mul h

Depends on / 依赖: _apply, blockDiagonal, split_ifs, transpose_apply
-/
protected theorem mul_sub (h : 0 < c -> c < b -> a != ∞) : a * (b - c) = a * b - a * c := by
  simp only [mul_comm a]
  exact ENNReal.sub_mul h

/--
theorem `sub_le_sub_iff_left` / 定理 `sub_le_sub_iff_left`

English:
theorem sub_le_sub_iff_left
  given: (h : c <= a) (h' : a != ∞)
  proof: (cancel_of_ne h').tsub_le_tsub_iff_left (cancel_of_ne (ne_top_of_le_ne_top h' h)) h

中文:
定理 sub_le_sub_iff_left
  条件: (h : c <= a) (h' : a != ∞)
  证明: (cancel_of_ne h').tsub_le_tsub_iff_left (cancel_of_ne (ne_top_of_le_ne_top h' h)) h

Depends on / 依赖: _map, _transpose, blockDiagonal, cancel_of_ne, conjTranspose, ne_top_of_le_ne_top, star_zero, tsub_le_tsub_iff_left
-/
theorem sub_le_sub_iff_left (h : c <= a) (h' : a != ∞) :
    (a - b <= a - c) ↔ c <= b :=
  (cancel_of_ne h').tsub_le_tsub_iff_left (cancel_of_ne (ne_top_of_le_ne_top h' h)) h

/--
theorem `le_toReal_sub` / 定理 `le_toReal_sub`

English:
theorem le_toReal_sub
  given: {a b : Real>=0∞} (hb : b != ∞)
  statement: a.toReal - b.toReal <= (a - b).toReal
  proof: by
  lift b to Real>=0 using hb
  induction a
  · simp
  · simp only [← coe_sub, NNReal.sub_def, Real.coe_toNNReal', coe_toReal]
    exact le_max_left _ _

@[simp]

中文:
定理 le_toReal_sub
  条件: {a b : 实数>=0∞} (hb : b != ∞)
  结论: a.to实数 - b.to实数 <= (a - b).to实数
  证明: by
  lift b to Real>=0 using hb
  induction a
  · simp
  · simp only [← coe_sub, NNReal.sub_def, Real.coe_toNNReal', coe_toReal]
    exact le_max_left _ _

@[simp]

Depends on / 依赖: NNReal, NNReal.sub_def, Real.coe_toNNReal, _apply, blockDiagonal, coe_sub, coe_toNNReal, coe_toReal, le_max_left, sub_def
-/
theorem le_toReal_sub {a b : Real>=0∞} (hb : b != ∞) : a.toReal - b.toReal <= (a - b).toReal := by
  lift b to Real>=0 using hb
  induction a
  · simp
  · simp only [← coe_sub, NNReal.sub_def, Real.coe_toNNReal', coe_toReal]
    exact le_max_left _ _

@[simp]
/--
lemma `toNNReal_sub` / 引理 `toNNReal_sub`

English:
lemma toNNReal_sub
  given: (hb : b != ∞)
  statement: (a - b).toNNReal = a.toNNReal - b.toNNReal
  proof: by
  lift b to Real>=0 using hb; induction a <;> simp [← coe_sub]

@[simp]

中文:
引理 toNNReal_sub
  条件: (hb : b != ∞)
  结论: (a - b).toNN实数 = a.toNN实数 - b.toNN实数
  证明: by
  lift b to Real>=0 using hb; induction a <;> simp [← coe_sub]

@[simp]

Depends on / 依赖: Decidable, Decidable.eq_or_ne, _apply, blockDiagonal, coe_sub, diagonal, eq_or_ne
-/
lemma toNNReal_sub (hb : b != ∞) : (a - b).toNNReal = a.toNNReal - b.toNNReal := by
  lift b to Real>=0 using hb; induction a <;> simp [← coe_sub]

@[simp]
/--
lemma `toReal_sub_of_le` / 引理 `toReal_sub_of_le`

English:
lemma toReal_sub_of_le
  given: (hba : b <= a) (ha : a != ∞)
  statement: (a - b).toReal = a.toReal - b.toReal
  proof: by
  simp [ENNReal.toReal, ne_top_of_le_ne_top ha hba, toNNReal_mono ha hba]

中文:
引理 toReal_sub_of_le
  条件: (hba : b <= a) (ha : a != ∞)
  结论: (a - b).to实数 = a.to实数 - b.to实数
  证明: by
  simp [ENNReal.toReal, ne_top_of_le_ne_top ha hba, toNNReal_mono ha hba]

Depends on / 依赖: ENNReal, ENNReal.toReal, _diagonal, blockDiagonal, diagonal, ne_top_of_le_ne_top, toNNReal_mono, toReal
-/
lemma toReal_sub_of_le (hba : b <= a) (ha : a != ∞) : (a - b).toReal = a.toReal - b.toReal := by
  simp [ENNReal.toReal, ne_top_of_le_ne_top ha hba, toNNReal_mono ha hba]

/--
theorem `ofReal_sub` / 定理 `ofReal_sub`

English:
theorem ofReal_sub
  given: (p : Real) {q : Real} (hq : 0 <= q)
  proof: by
  obtain h | h := le_total p q
  · rw [ofReal_of_nonpos (sub_nonpos_of_le h), tsub_eq_zero_of_le (ofReal_le_ofReal h)]
  refine ENNReal.eq_sub_of_add_eq ofReal_ne_top ?_
  rw [← ofReal_add (sub_nonneg_of_le h) hq]; rw [sub_add_cancel]

中文:
定理 ofReal_sub
  条件: (p : 实数) {q : 实数} (hq : 0 <= q)
  证明: by
  obtain h | h := le_total p q
  · rw [ofReal_of_nonpos (sub_nonpos_of_le h), tsub_eq_zero_of_le (ofReal_le_ofReal h)]
  refine ENNReal.eq_sub_of_add_eq ofReal_ne_top ?_
  rw [← ofReal_add (sub_nonneg_of_le h) hq]; rw [sub_add_cancel]

Depends on / 依赖: ENNReal, ENNReal.eq_sub_of_add_eq, Pi.add_apply, _apply, add_apply, blockDiagonal, eq_sub_of_add_eq, le_total, ofReal_add, ofReal_le_ofReal, ofReal_ne_top, ofReal_of_nonpos, split_ifs, sub_add_cancel, sub_nonneg_of_le, sub_nonpos_of_le, tsub_eq_zero_of_le
-/
theorem ofReal_sub (p : Real) {q : Real} (hq : 0 <= q) :
    ENNReal.ofReal (p - q) = ENNReal.ofReal p - ENNReal.ofReal q := by
  obtain h | h := le_total p q
  · rw [ofReal_of_nonpos (sub_nonpos_of_le h), tsub_eq_zero_of_le (ofReal_le_ofReal h)]
  refine ENNReal.eq_sub_of_add_eq ofReal_ne_top ?_
  rw [← ofReal_add (sub_nonneg_of_le h) hq]; rw [sub_add_cancel]

/--
lemma `sub_sub_sub_cancel_left` / 引理 `sub_sub_sub_cancel_left`

English:
lemma sub_sub_sub_cancel_left
  given: (ha : a != ∞) (h : b <= a)
  statement: a - c - (a - b) = b - c
  proof: by
  have hb : b != ∞ := ne_top_of_le_ne_top ha h
  lift a to Real>=0 using ha
  lift b to Real>=0 using hb
  cases c
  · simp
  · norm_cast
    rw [tsub_tsub_tsub_cancel_left]
    exact mod_cast h

中文:
引理 sub_sub_sub_cancel_left
  条件: (ha : a != ∞) (h : b <= a)
  结论: a - c - (a - b) = b - c
  证明: by
  have hb : b != ∞ := ne_top_of_le_ne_top ha h
  lift a to Real>=0 using ha
  lift b to Real>=0 using hb
  cases c
  · simp
  · norm_cast
    rw [tsub_tsub_tsub_cancel_left]
    exact mod_cast h

Depends on / 依赖: blockDiagonal, mod_cast, ne_top_of_le_ne_top, tsub_tsub_tsub_cancel_left
-/
lemma sub_sub_sub_cancel_left (ha : a != ∞) (h : b <= a) : a - c - (a - b) = b - c := by
  have hb : b != ∞ := ne_top_of_le_ne_top ha h
  lift a to Real>=0 using ha
  lift b to Real>=0 using hb
  cases c
  · simp
  · norm_cast
    rw [tsub_tsub_tsub_cancel_left]
    exact mod_cast h

end Sub

section Interval

variable {x y z : Real>=0∞} {ε ε₁ ε₂ : Real>=0∞} {s : Set Real>=0∞}

/--
theorem `Ico_eq_Iio` / 定理 `Ico_eq_Iio`

English:
theorem Ico_eq_Iio
  statement: Ico 0 y = Iio y
  proof: Ico_bot

中文:
定理 Ico_eq_Iio
  结论: Ico 0 y = Iio y
  证明: Ico_bot

Depends on / 依赖: AddMonoidHom, blockDiagonal, map_neg
-/
protected theorem Ico_eq_Iio : Ico 0 y = Iio y :=
  Ico_bot

/--
theorem `mem_Iio_self_add` / 定理 `mem_Iio_self_add`

English:
theorem mem_Iio_self_add
  statement: x != ∞ -> ε != 0 -> x in Iio (x + ε)
  proof: fun xt ε0 => lt_add_right xt ε0

中文:
定理 mem_Iio_self_add
  结论: x != ∞ -> ε != 0 -> x in Iio (x + ε)
  证明: fun xt ε0 => lt_add_right xt ε0

Depends on / 依赖: AddMonoidHom, blockDiagonal, lt_add_right, map_sub
-/
theorem mem_Iio_self_add : x != ∞ -> ε != 0 -> x in Iio (x + ε) := fun xt ε0 => lt_add_right xt ε0

/--
theorem `mem_Ioo_self_sub_add` / 定理 `mem_Ioo_self_sub_add`

English:
theorem mem_Ioo_self_sub_add
  statement: x != ∞ -> x != 0 -> ε₁ != 0 -> ε₂ != 0 -> x in Ioo (x - ε₁) (x + ε₂)
  proof: fun xt x0 ε0 ε0' => ⟨ENNReal.sub_lt_self xt x0 ε0, lt_add_right xt ε0'⟩

@[simp]

中文:
定理 mem_Ioo_self_sub_add
  结论: x != ∞ -> x != 0 -> ε₁ != 0 -> ε₂ != 0 -> x in Ioo (x - ε₁) (x + ε₂)
  证明: fun xt x0 ε0 ε0' => ⟨ENNReal.sub_lt_self xt x0 ε0, lt_add_right xt ε0'⟩

@[simp]

Depends on / 依赖: ENNReal, ENNReal.sub_lt_self, Finset, Finset.sum_eq_zero, Finset.sum_sigma, Finset.univ_sigma_univ, Fintype, Fintype.sum_eq_single, _apply, blockDiagonal, dif_neg, dif_pos, lt_add_right, mul_apply, split_ifs, sub_lt_self, sum_eq_single, sum_eq_zero, sum_sigma, univ_sigma_univ
-/
theorem mem_Ioo_self_sub_add : x != ∞ -> x != 0 -> ε₁ != 0 -> ε₂ != 0 -> x in Ioo (x - ε₁) (x + ε₂) :=
  fun xt x0 ε0 ε0' => ⟨ENNReal.sub_lt_self xt x0 ε0, lt_add_right xt ε0'⟩

@[simp]
/--
theorem `image_coe_Iic` / 定理 `image_coe_Iic`

English:
theorem image_coe_Iic
  given: (x : Real>=0)
  statement: (↑) '' Iic x = Iic (x : Real>=0∞)
  proof: WithTop.image_coe_Iic

@[simp]

中文:
定理 image_coe_Iic
  条件: (x : 实数>=0)
  结论: (↑) '' Iic x = Iic (x : 实数>=0∞)
  证明: WithTop.image_coe_Iic

@[simp]

Depends on / 依赖: AddMonoidHom, WithTop, WithTop.image_coe_Iic, _mul, _one, blockDiagonal, image_coe_Iic, map_mul, map_one
-/
theorem image_coe_Iic (x : Real>=0) : (↑) '' Iic x = Iic (x : Real>=0∞) := WithTop.image_coe_Iic

@[simp]
/--
theorem `image_coe_Ici` / 定理 `image_coe_Ici`

English:
theorem image_coe_Ici
  given: (x : Real>=0)
  statement: (↑) '' Ici x = Ico ↑x ∞
  proof: WithTop.image_coe_Ici

@[simp]

中文:
定理 image_coe_Ici
  条件: (x : 实数>=0)
  结论: (↑) '' Ici x = Ico ↑x ∞
  证明: WithTop.image_coe_Ici

@[simp]

Depends on / 依赖: RingHom, WithTop, WithTop.image_coe_Ici, blockDiagonal, image_coe_Ici, map_pow
-/
theorem image_coe_Ici (x : Real>=0) : (↑) '' Ici x = Ico ↑x ∞ := WithTop.image_coe_Ici

@[simp]
/--
theorem `image_coe_Iio` / 定理 `image_coe_Iio`

English:
theorem image_coe_Iio
  given: (x : Real>=0)
  statement: (↑) '' Iio x = Iio (x : Real>=0∞)
  proof: WithTop.image_coe_Iio

@[simp]

中文:
定理 image_coe_Iio
  条件: (x : 实数>=0)
  结论: (↑) '' Iio x = Iio (x : 实数>=0∞)
  证明: WithTop.image_coe_Iio

@[simp]

Depends on / 依赖: Pi.smul_apply, WithTop, WithTop.image_coe_Iio, _apply, blockDiagonal, image_coe_Iio, smul_apply, split_ifs
-/
theorem image_coe_Iio (x : Real>=0) : (↑) '' Iio x = Iio (x : Real>=0∞) := WithTop.image_coe_Iio

@[simp]
/--
theorem `image_coe_Ioi` / 定理 `image_coe_Ioi`

English:
theorem image_coe_Ioi
  given: (x : Real>=0)
  statement: (↑) '' Ioi x = Ioo ↑x ∞
  proof: WithTop.image_coe_Ioi

@[simp]

中文:
定理 image_coe_Ioi
  条件: (x : 实数>=0)
  结论: (↑) '' Ioi x = Ioo ↑x ∞
  证明: WithTop.image_coe_Ioi

@[simp]

Depends on / 依赖: WithTop, WithTop.image_coe_Ioi, image_coe_Ioi
-/
theorem image_coe_Ioi (x : Real>=0) : (↑) '' Ioi x = Ioo ↑x ∞ := WithTop.image_coe_Ioi

@[simp]
/--
theorem `image_coe_Icc` / 定理 `image_coe_Icc`

English:
theorem image_coe_Icc
  given: (x y : Real>=0)
  statement: (↑) '' Icc x y = Icc (x : Real>=0∞) y
  proof: WithTop.image_coe_Icc

@[simp]

中文:
定理 image_coe_Icc
  条件: (x y : 实数>=0)
  结论: (↑) '' Icc x y = Icc (x : 实数>=0∞) y
  证明: WithTop.image_coe_Icc

@[simp]

Depends on / 依赖: WithTop, WithTop.image_coe_Icc, image_coe_Icc
-/
theorem image_coe_Icc (x y : Real>=0) : (↑) '' Icc x y = Icc (x : Real>=0∞) y := WithTop.image_coe_Icc

@[simp]
/--
theorem `image_coe_Ico` / 定理 `image_coe_Ico`

English:
theorem image_coe_Ico
  given: (x y : Real>=0)
  statement: (↑) '' Ico x y = Ico (x : Real>=0∞) y
  proof: WithTop.image_coe_Ico

@[simp]

中文:
定理 image_coe_Ico
  条件: (x y : 实数>=0)
  结论: (↑) '' Ico x y = Ico (x : 实数>=0∞) y
  证明: WithTop.image_coe_Ico

@[simp]

Depends on / 依赖: WithTop, WithTop.image_coe_Ico, image_coe_Ico
-/
theorem image_coe_Ico (x y : Real>=0) : (↑) '' Ico x y = Ico (x : Real>=0∞) y := WithTop.image_coe_Ico

@[simp]
/--
theorem `image_coe_Ioc` / 定理 `image_coe_Ioc`

English:
theorem image_coe_Ioc
  given: (x y : Real>=0)
  statement: (↑) '' Ioc x y = Ioc (x : Real>=0∞) y
  proof: WithTop.image_coe_Ioc

@[simp]

中文:
定理 image_coe_Ioc
  条件: (x y : 实数>=0)
  结论: (↑) '' Ioc x y = Ioc (x : 实数>=0∞) y
  证明: WithTop.image_coe_Ioc

@[simp]

Depends on / 依赖: WithTop, WithTop.image_coe_Ioc, image_coe_Ioc
-/
theorem image_coe_Ioc (x y : Real>=0) : (↑) '' Ioc x y = Ioc (x : Real>=0∞) y := WithTop.image_coe_Ioc

@[simp]
/--
theorem `image_coe_Ioo` / 定理 `image_coe_Ioo`

English:
theorem image_coe_Ioo
  given: (x y : Real>=0)
  statement: (↑) '' Ioo x y = Ioo (x : Real>=0∞) y
  proof: WithTop.image_coe_Ioo

@[simp]

中文:
定理 image_coe_Ioo
  条件: (x y : 实数>=0)
  结论: (↑) '' Ioo x y = Ioo (x : 实数>=0∞) y
  证明: WithTop.image_coe_Ioo

@[simp]

Depends on / 依赖: WithTop, WithTop.image_coe_Ioo, image_coe_Ioo
-/
theorem image_coe_Ioo (x y : Real>=0) : (↑) '' Ioo x y = Ioo (x : Real>=0∞) y := WithTop.image_coe_Ioo

@[simp]
/--
theorem `image_coe_uIcc` / 定理 `image_coe_uIcc`

English:
theorem image_coe_uIcc
  given: (x y : Real>=0)
  statement: (↑) '' uIcc x y = uIcc (x : Real>=0∞) y
  proof: by simp [uIcc]

@[simp]

中文:
定理 image_coe_uIcc
  条件: (x y : 实数>=0)
  结论: (↑) '' uIcc x y = uIcc (x : 实数>=0∞) y
  证明: by simp [uIcc]

@[simp]
-/
theorem image_coe_uIcc (x y : Real>=0) : (↑) '' uIcc x y = uIcc (x : Real>=0∞) y := by simp [uIcc]

@[simp]
/--
theorem `image_coe_uIoc` / 定理 `image_coe_uIoc`

English:
theorem image_coe_uIoc
  given: (x y : Real>=0)
  statement: (↑) '' uIoc x y = uIoc (x : Real>=0∞) y
  proof: by simp [uIoc]

@[simp]

中文:
定理 image_coe_uIoc
  条件: (x y : 实数>=0)
  结论: (↑) '' uIoc x y = uIoc (x : 实数>=0∞) y
  证明: by simp [uIoc]

@[simp]

Depends on / 依赖: Decidable, Decidable.eq_or_ne, _apply, blockDiag, diagonal_apply_eq, diagonal_apply_ne, eq_or_ne
-/
theorem image_coe_uIoc (x y : Real>=0) : (↑) '' uIoc x y = uIoc (x : Real>=0∞) y := by simp [uIoc]

@[simp]
/--
theorem `image_coe_uIoo` / 定理 `image_coe_uIoo`

English:
theorem image_coe_uIoo
  given: (x y : Real>=0)
  statement: (↑) '' uIoo x y = uIoo (x : Real>=0∞) y
  proof: by simp [uIoo]

中文:
定理 image_coe_uIoo
  条件: (x y : 实数>=0)
  结论: (↑) '' uIoo x y = uIoo (x : 实数>=0∞) y
  证明: by simp [uIoo]

Depends on / 依赖: _apply_eq, blockDiagonal
-/
theorem image_coe_uIoo (x y : Real>=0) : (↑) '' uIoo x y = uIoo (x : Real>=0∞) y := by simp [uIoo]

end Interval

section iInf

variable {ι : Sort*} {f g : ι -> Real>=0∞}
variable {a b c d : Real>=0∞} {r p q : Real>=0}

/--
theorem `toNNReal_iInf` / 定理 `toNNReal_iInf`

English:
theorem toNNReal_iInf
  given: (hf : forall i, f i != ∞)
  statement: (iInf f).toNNReal = ⨅ i, (f i).toNNReal
  proof: by
  cases isEmpty_or_nonempty ι
  · rw [iInf_of_empty, toNNReal_top, NNReal.iInf_empty]
  · lift f to ι -> Real>=0 using hf
    simp_rw [← coe_iInf, toNNReal_coe]

中文:
定理 toNNReal_iInf
  条件: (hf : 对任意 i, f i != ∞)
  结论: (iInf f).toNN实数 = ⨅ i, (f i).toNN实数
  证明: by
  cases isEmpty_or_nonempty ι
  · rw [iInf_of_empty, toNNReal_top, NNReal.iInf_empty]
  · lift f to ι -> Real>=0 using hf
    simp_rw [← coe_iInf, toNNReal_coe]

Depends on / 依赖: Function, Function.LeftInverse.injective, LeftInverse, NNReal, NNReal.iInf_empty, _blockDiagonal, blockDiag, coe_iInf, iInf_empty, iInf_of_empty, injective, isEmpty_or_nonempty, simp_rw, toNNReal_coe, toNNReal_top
-/
theorem toNNReal_iInf (hf : forall i, f i != ∞) : (iInf f).toNNReal = ⨅ i, (f i).toNNReal := by
  cases isEmpty_or_nonempty ι
  · rw [iInf_of_empty, toNNReal_top, NNReal.iInf_empty]
  · lift f to ι -> Real>=0 using hf
    simp_rw [← coe_iInf, toNNReal_coe]

/--
theorem `toNNReal_sInf` / 定理 `toNNReal_sInf`

English:
theorem toNNReal_sInf
  given: (s : Set Real>=0∞) (hs : forall r in s, r != ∞)
  proof: by
  have hf : forall i, ((↑) : s -> Real>=0∞) i != ∞ := fun ⟨r, rs⟩ => hs r rs
  simpa only [← sInf_range, ← image_eq_range, Subtype.range_coe_subtype] using! (toNNReal_iInf hf)

中文:
定理 toNNReal_sInf
  条件: (s : Set 实数>=0∞) (hs : 对任意 r in s, r != ∞)
  证明: by
  have hf : forall i, ((↑) : s -> Real>=0∞) i != ∞ := fun ⟨r, rs⟩ => hs r rs
  simpa only [← sInf_range, ← image_eq_range, Subtype.range_coe_subtype] using! (toNNReal_iInf hf)

Depends on / 依赖: Subtype, Subtype.range_coe_subtype, _injective, _injective.eq_iff, blockDiagonal, eq_iff, image_eq_range, range_coe_subtype, sInf_range, toNNReal_iInf
-/
theorem toNNReal_sInf (s : Set Real>=0∞) (hs : forall r in s, r != ∞) :
    (sInf s).toNNReal = sInf (ENNReal.toNNReal '' s) := by
  have hf : forall i, ((↑) : s -> Real>=0∞) i != ∞ := fun ⟨r, rs⟩ => hs r rs
  simpa only [← sInf_range, ← image_eq_range, Subtype.range_coe_subtype] using! (toNNReal_iInf hf)

/--
theorem `toReal_iInf` / 定理 `toReal_iInf`

English:
theorem toReal_iInf
  given: (hf : forall i, f i != ∞)
  statement: (iInf f).toReal = ⨅ i, (f i).toReal
  proof: by
  simp only [ENNReal.toReal, toNNReal_iInf hf, NNReal.coe_iInf]

中文:
定理 toReal_iInf
  条件: (hf : 对任意 i, f i != ∞)
  结论: (iInf f).to实数 = ⨅ i, (f i).to实数
  证明: by
  simp only [ENNReal.toReal, toNNReal_iInf hf, NNReal.coe_iInf]

Depends on / 依赖: ENNReal, ENNReal.toReal, NNReal, NNReal.coe_iInf, _diagonal, blockDiag, coe_iInf, toNNReal_iInf, toReal
-/
theorem toReal_iInf (hf : forall i, f i != ∞) : (iInf f).toReal = ⨅ i, (f i).toReal := by
  simp only [ENNReal.toReal, toNNReal_iInf hf, NNReal.coe_iInf]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `toReal_sInf` / 定理 `toReal_sInf`

English:
theorem toReal_sInf
  given: (s : Set Real>=0∞) (hf : forall r in s, r != ∞)
  proof: by
  simp only [ENNReal.toReal, toNNReal_sInf s hf, NNReal.coe_sInf, Set.image_image]

中文:
定理 toReal_sInf
  条件: (s : Set 实数>=0∞) (hf : 对任意 r in s, r != ∞)
  证明: by
  simp only [ENNReal.toReal, toNNReal_sInf s hf, NNReal.coe_sInf, Set.image_image]

Depends on / 依赖: ENNReal, ENNReal.toReal, NNReal, NNReal.coe_sInf, Set.image_image, coe_sInf, image_image, toNNReal_sInf, toReal
-/
theorem toReal_sInf (s : Set Real>=0∞) (hf : forall r in s, r != ∞) :
    (sInf s).toReal = sInf (ENNReal.toReal '' s) := by
  simp only [ENNReal.toReal, toNNReal_sInf s hf, NNReal.coe_sInf, Set.image_image]

/--
lemma `ofReal_iInf` / 引理 `ofReal_iInf`

English:
lemma ofReal_iInf
  given: [Nonempty ι] (f : ι -> Real)
  proof: by
  obtain ⟨i, hi⟩ | h := em (exists i, f i <= 0)
  · rw [iInf_eq_bot.2 fun _ _ => ⟨i, by simpa [ofReal_of_nonpos hi]⟩]
    simp [Real.iInf_nonpos' ⟨i, hi⟩]
  replace h i : 0 <= f i := le_of_not_ge fun hi => h ⟨i, hi⟩
  refine eq_of_forall_le_iff fun a => ?_
  obtain rfl | ha := eq_or_ne a ∞
  · si

中文:
引理 ofReal_iInf
  条件: [Nonempty ι] (f : ι -> 实数)
  证明: by
  obtain ⟨i, hi⟩ | h := em (exists i, f i <= 0)
  · rw [iInf_eq_bot.2 fun _ _ => ⟨i, by simpa [ofReal_of_nonpos hi]⟩]
    simp [Real.iInf_nonpos' ⟨i, hi⟩]
  replace h i : 0 <= f i := le_of_not_ge fun hi => h ⟨i, hi⟩
  refine eq_of_forall_le_iff fun a => ?_
  obtain rfl | ha := eq_or_ne a ∞
  · si

Depends on / 依赖: blockDiag
-/
@[simp] lemma ofReal_iInf [Nonempty ι] (f : ι -> Real) :
    ENNReal.ofReal (⨅ i, f i) = ⨅ i, ENNReal.ofReal (f i) := by
  obtain ⟨i, hi⟩ | h := em (exists i, f i <= 0)
  · rw [iInf_eq_bot.2 fun _ _ => ⟨i, by simpa [ofReal_of_nonpos hi]⟩]
    simp [Real.iInf_nonpos' ⟨i, hi⟩]
  replace h i : 0 <= f i := le_of_not_ge fun hi => h ⟨i, hi⟩
  refine eq_of_forall_le_iff fun a => ?_
  obtain rfl | ha := eq_or_ne a ∞
  · simp
  rw [le_iInf_iff]; rw [le_ofReal_iff_toReal_le ha]; rw [le_ciInf_iff ⟨0]; rw [by simpa [mem_lowerBounds]⟩]
  · exact forall_congr' fun i => (le_ofReal_iff_toReal_le ha (h _)).symm
  · exact Real.iInf_nonneg h

/--
theorem `iInf_add` / 定理 `iInf_add`

English:
theorem iInf_add
  statement: iInf f + a = ⨅ i, f i + a
  proof: le_antisymm (le_iInf fun _ => add_le_add (iInf_le _ _) <| le_rfl)
    (tsub_le_iff_right.1 <| le_iInf fun _ => tsub_le_iff_right.2 <| iInf_le _ _)

中文:
定理 iInf_add
  结论: iInf f + a = ⨅ i, f i + a
  证明: le_antisymm (le_iInf fun _ => add_le_add (iInf_le _ _) <| le_rfl)
    (tsub_le_iff_right.1 <| le_iInf fun _ => tsub_le_iff_right.2 <| iInf_le _ _)

Depends on / 依赖: AddMonoidHom, add_le_add, blockDiag, iInf_le, le_antisymm, le_iInf, le_rfl, map_neg, tsub_le_iff_right
-/
theorem iInf_add : iInf f + a = ⨅ i, f i + a :=
  le_antisymm (le_iInf fun _ => add_le_add (iInf_le _ _) <| le_rfl)
    (tsub_le_iff_right.1 <| le_iInf fun _ => tsub_le_iff_right.2 <| iInf_le _ _)

/--
theorem `sub_iInf` / 定理 `sub_iInf`

English:
theorem sub_iInf
  statement: (a - ⨅ i, f i) = ⨆ i, a - f i
  proof: by
  refine eq_of_forall_ge_iff fun c => ?_
  rw [tsub_le_iff_right]; rw [add_comm]; rw [iInf_add]
  simp [tsub_le_iff_right, add_comm]

中文:
定理 sub_iInf
  结论: (a - ⨅ i, f i) = ⨆ i, a - f i
  证明: by
  refine eq_of_forall_ge_iff fun c => ?_
  rw [tsub_le_iff_right]; rw [add_comm]; rw [iInf_add]
  simp [tsub_le_iff_right, add_comm]

Depends on / 依赖: AddMonoidHom, add_comm, blockDiag, eq_of_forall_ge_iff, iInf_add, map_sub, tsub_le_iff_right
-/
theorem sub_iInf : (a - ⨅ i, f i) = ⨆ i, a - f i := by
  refine eq_of_forall_ge_iff fun c => ?_
  rw [tsub_le_iff_right]; rw [add_comm]; rw [iInf_add]
  simp [tsub_le_iff_right, add_comm]

/--
theorem `sInf_add` / 定理 `sInf_add`

English:
theorem sInf_add
  given: {s : Set Real>=0∞}
  statement: sInf s + a = ⨅ b in s, b + a
  proof: by simp [sInf_eq_iInf, iInf_add]

中文:
定理 sInf_add
  条件: {s : Set 实数>=0∞}
  结论: sInf s + a = ⨅ b in s, b + a
  证明: by simp [sInf_eq_iInf, iInf_add]

Depends on / 依赖: iInf_add, sInf_eq_iInf
-/
theorem sInf_add {s : Set Real>=0∞} : sInf s + a = ⨅ b in s, b + a := by simp [sInf_eq_iInf, iInf_add]

/--
theorem `add_iInf` / 定理 `add_iInf`

English:
theorem add_iInf
  given: {a : Real>=0∞}
  statement: a + iInf f = ⨅ b, a + f b
  proof: by
  rw [add_comm]; rw [iInf_add]; simp [add_comm]

中文:
定理 add_iInf
  条件: {a : 实数>=0∞}
  结论: a + iInf f = ⨅ b, a + f b
  证明: by
  rw [add_comm]; rw [iInf_add]; simp [add_comm]

Depends on / 依赖: add_comm, iInf_add
-/
theorem add_iInf {a : Real>=0∞} : a + iInf f = ⨅ b, a + f b := by
  rw [add_comm]; rw [iInf_add]; simp [add_comm]

/--
theorem `iInf_add_iInf` / 定理 `iInf_add_iInf`

English:
theorem iInf_add_iInf
  given: (h : forall i j, exists k, f k + g k <= f i + g j)
  statement: iInf f + iInf g = ⨅ a, f a + g a
  proof: suffices ⨅ a, f a + g a <= iInf f + iInf g from
    le_antisymm (le_iInf fun _ => add_le_add (iInf_le _ _) (iInf_le _ _)) this
  calc
    ⨅ a, f a + g a <= ⨅ (a) (a'), f a + g a' :=
      le_iInf₂ fun a a' => let ⟨k, h⟩ := h a a'; iInf_le_of_le k h
    _ = iInf f + iInf g := by simp_rw [iInf_add, ad

中文:
定理 iInf_add_iInf
  条件: (h : 对任意 i j, 存在 k, f k + g k <= f i + g j)
  结论: iInf f + iInf g = ⨅ a, f a + g a
  证明: suffices ⨅ a, f a + g a <= iInf f + iInf g from
    le_antisymm (le_iInf fun _ => add_le_add (iInf_le _ _) (iInf_le _ _)) this
  calc
    ⨅ a, f a + g a <= ⨅ (a) (a'), f a + g a' :=
      le_iInf₂ fun a a' => let ⟨k, h⟩ := h a a'; iInf_le_of_le k h
    _ = iInf f + iInf g := by simp_rw [iInf_add, ad

Depends on / 依赖: add_iInf, add_le_add, iInf_add, iInf_le, iInf_le_of_le, le_antisymm, le_iInf, simp_rw
-/
theorem iInf_add_iInf (h : forall i j, exists k, f k + g k <= f i + g j) : iInf f + iInf g = ⨅ a, f a + g a :=
  suffices ⨅ a, f a + g a <= iInf f + iInf g from
    le_antisymm (le_iInf fun _ => add_le_add (iInf_le _ _) (iInf_le _ _)) this
  calc
    ⨅ a, f a + g a <= ⨅ (a) (a'), f a + g a' :=
      le_iInf₂ fun a a' => let ⟨k, h⟩ := h a a'; iInf_le_of_le k h
    _ = iInf f + iInf g := by simp_rw [iInf_add, add_iInf]

/--
lemma `iInf_add_iInf_of_monotone` / 引理 `iInf_add_iInf_of_monotone`

English:
lemma iInf_add_iInf_of_monotone
  statement: {ι : Type*} [Preorder ι] [IsCodirectedOrder ι] {f g : ι -> Real>=0∞}
  proof: iInf_add_iInf fun i j => (exists_le_le i j).imp fun _k ⟨hi, hj⟩ => by gcongr <;> apply_rules

中文:
引理 iInf_add_iInf_of_monotone
  结论: {ι : 类型} [Preorder ι] [IsCodirectedOrder ι] {f g : ι -> 实数>=0∞}
  证明: iInf_add_iInf fun i j => (exists_le_le i j).imp fun _k ⟨hi, hj⟩ => by gcongr <;> apply_rules

Depends on / 依赖: apply_rules, exists_le_le, iInf_add_iInf
-/
lemma iInf_add_iInf_of_monotone {ι : Type*} [Preorder ι] [IsCodirectedOrder ι] {f g : ι -> Real>=0∞}
    (hf : Monotone f) (hg : Monotone g) : iInf f + iInf g = ⨅ a, f a + g a :=
  iInf_add_iInf fun i j => (exists_le_le i j).imp fun _k ⟨hi, hj⟩ => by gcongr <;> apply_rules

/--
lemma `add_iInf₂` / 引理 `add_iInf₂`

English:
lemma add_iInf₂
  given: {κ : ι -> Sort*} (f : (i : ι) -> κ i -> Real>=0∞)
  proof: by
  simp [add_iInf]

中文:
引理 add_iInf₂
  条件: {κ : ι -> Sort*} (f : (i : ι) -> κ i -> 实数>=0∞)
  证明: by
  simp [add_iInf]

Depends on / 依赖: add_iInf
-/
lemma add_iInf₂ {κ : ι -> Sort*} (f : (i : ι) -> κ i -> Real>=0∞) :
    a + ⨅ (i) (j), f i j = ⨅ (i) (j), a + f i j := by
  simp [add_iInf]

/--
lemma `iInf₂_add` / 引理 `iInf₂_add`

English:
lemma iInf₂_add
  given: {κ : ι -> Sort*} (f : (i : ι) -> κ i -> Real>=0∞)
  proof: by
  simp only [add_comm, add_iInf₂]

中文:
引理 iInf₂_add
  条件: {κ : ι -> Sort*} (f : (i : ι) -> κ i -> 实数>=0∞)
  证明: by
  simp only [add_comm, add_iInf₂]

Depends on / 依赖: add_comm
-/
lemma iInf₂_add {κ : ι -> Sort*} (f : (i : ι) -> κ i -> Real>=0∞) :
    (⨅ (i) (j), f i j) + a = ⨅ (i) (j), f i j + a := by
  simp only [add_comm, add_iInf₂]

/--
lemma `add_sInf` / 引理 `add_sInf`

English:
lemma add_sInf
  given: {s : Set Real>=0∞}
  statement: a + sInf s = ⨅ b in s, a + b
  proof: by
  rw [sInf_eq_iInf]; rw [add_iInf₂]

中文:
引理 add_sInf
  条件: {s : Set 实数>=0∞}
  结论: a + sInf s = ⨅ b in s, a + b
  证明: by
  rw [sInf_eq_iInf]; rw [add_iInf₂]

Depends on / 依赖: sInf_eq_iInf
-/
lemma add_sInf {s : Set Real>=0∞} : a + sInf s = ⨅ b in s, a + b := by
  rw [sInf_eq_iInf]; rw [add_iInf₂]

variable {κ : Sort*}

/--
lemma `le_iInf_add_iInf` / 引理 `le_iInf_add_iInf`

English:
lemma le_iInf_add_iInf
  given: {g : κ -> Real>=0∞} (h : forall i j, a <= f i + g j)
  proof: by
  simp_rw [iInf_add, add_iInf]; exact le_iInf₂ h

中文:
引理 le_iInf_add_iInf
  条件: {g : κ -> 实数>=0∞} (h : 对任意 i j, a <= f i + g j)
  证明: by
  simp_rw [iInf_add, add_iInf]; exact le_iInf₂ h

Depends on / 依赖: add_iInf, iInf_add, simp_rw
-/
lemma le_iInf_add_iInf {g : κ -> Real>=0∞} (h : forall i j, a <= f i + g j) :
    a <= iInf f + iInf g := by
  simp_rw [iInf_add, add_iInf]; exact le_iInf₂ h

/--
lemma `le_iInf₂_add_iInf₂` / 引理 `le_iInf₂_add_iInf₂`

English:
lemma le_iInf₂_add_iInf₂
  statement: {q₁ : ι -> Sort*} {q₂ : κ -> Sort*}
  proof: by
  simp_rw [iInf₂_add, add_iInf₂]
  exact le_iInf₂ fun i hi => le_iInf₂ (h i hi)

中文:
引理 le_iInf₂_add_iInf₂
  结论: {q₁ : ι -> Sort*} {q₂ : κ -> Sort*}
  证明: by
  simp_rw [iInf₂_add, add_iInf₂]
  exact le_iInf₂ fun i hi => le_iInf₂ (h i hi)

Depends on / 依赖: simp_rw
-/
lemma le_iInf₂_add_iInf₂ {q₁ : ι -> Sort*} {q₂ : κ -> Sort*}
    {f : (i : ι) -> q₁ i -> Real>=0∞} {g : (k : κ) -> q₂ k -> Real>=0∞}
    (h : forall i pi k qk, a <= f i pi + g k qk) :
    a <= (⨅ (i) (qi), f i qi) + ⨅ (k) (qk), g k qk := by
  simp_rw [iInf₂_add, add_iInf₂]
  exact le_iInf₂ fun i hi => le_iInf₂ (h i hi)

/--
lemma `iInf_gt_eq_self` / 引理 `iInf_gt_eq_self`

English:
lemma iInf_gt_eq_self
  given: (a : Real>=0∞)
  statement: ⨅ b, ⨅ _ : a < b, b = a
  proof: by
  refine le_antisymm ?_ (le_iInf₂ fun b hb => hb.le)
  refine le_of_forall_gt fun c hac => ?_
  obtain ⟨d, had, hdc⟩ := exists_between hac
  exact (iInf₂_le_of_le d had le_rfl).trans_lt hdc

中文:
引理 iInf_gt_eq_self
  条件: (a : 实数>=0∞)
  结论: ⨅ b, ⨅ _ : a < b, b = a
  证明: by
  refine le_antisymm ?_ (le_iInf₂ fun b hb => hb.le)
  refine le_of_forall_gt fun c hac => ?_
  obtain ⟨d, had, hdc⟩ := exists_between hac
  exact (iInf₂_le_of_le d had le_rfl).trans_lt hdc
-/
@[simp] lemma iInf_gt_eq_self (a : Real>=0∞) : ⨅ b, ⨅ _ : a < b, b = a := by
  refine le_antisymm ?_ (le_iInf₂ fun b hb => hb.le)
  refine le_of_forall_gt fun c hac => ?_
  obtain ⟨d, had, hdc⟩ := exists_between hac
  exact (iInf₂_le_of_le d had le_rfl).trans_lt hdc

/--
lemma `exists_add_lt_of_add_lt` / 引理 `exists_add_lt_of_add_lt`

English:
lemma exists_add_lt_of_add_lt
  given: {x y z : Real>=0∞} (h : y + z < x)
  proof: by
  contrapose! h
  simpa using le_iInf₂_add_iInf₂ h

中文:
引理 exists_add_lt_of_add_lt
  条件: {x y z : 实数>=0∞} (h : y + z < x)
  证明: by
  contrapose! h
  simpa using le_iInf₂_add_iInf₂ h

Depends on / 依赖: contrapose
-/
lemma exists_add_lt_of_add_lt {x y z : Real>=0∞} (h : y + z < x) :
    exists y' > y, exists z' > z, y' + z' < x := by
  contrapose! h
  simpa using le_iInf₂_add_iInf₂ h

end iInf

section iSup

variable {ι κ : Sort*} {f g : ι -> Real>=0∞} {s : Set Real>=0∞} {a : Real>=0∞}

/--
theorem `toNNReal_iSup` / 定理 `toNNReal_iSup`

English:
theorem toNNReal_iSup
  given: (hf : forall i, f i != ∞)
  statement: (iSup f).toNNReal = ⨆ i, (f i).toNNReal
  proof: by
  lift f to ι -> Real>=0 using hf
  simp_rw [toNNReal_coe]
  by_cases h : BddAbove (range f)
  · rw [← coe_iSup h, toNNReal_coe]
  · rw [NNReal.iSup_of_not_bddAbove h, iSup_coe_eq_top.2 h, toNNReal_top]

中文:
定理 toNNReal_iSup
  条件: (hf : 对任意 i, f i != ∞)
  结论: (iSup f).toNN实数 = ⨆ i, (f i).toNN实数
  证明: by
  lift f to ι -> Real>=0 using hf
  simp_rw [toNNReal_coe]
  by_cases h : BddAbove (range f)
  · rw [← coe_iSup h, toNNReal_coe]
  · rw [NNReal.iSup_of_not_bddAbove h, iSup_coe_eq_top.2 h, toNNReal_top]

Depends on / 依赖: BddAbove, NNReal, NNReal.iSup_of_not_bddAbove, coe_iSup, iSup_coe_eq_top, iSup_of_not_bddAbove, simp_rw, toNNReal_coe, toNNReal_top
-/
theorem toNNReal_iSup (hf : forall i, f i != ∞) : (iSup f).toNNReal = ⨆ i, (f i).toNNReal := by
  lift f to ι -> Real>=0 using hf
  simp_rw [toNNReal_coe]
  by_cases h : BddAbove (range f)
  · rw [← coe_iSup h, toNNReal_coe]
  · rw [NNReal.iSup_of_not_bddAbove h, iSup_coe_eq_top.2 h, toNNReal_top]

/--
theorem `toNNReal_sSup` / 定理 `toNNReal_sSup`

English:
theorem toNNReal_sSup
  given: (s : Set Real>=0∞) (hs : forall r in s, r != ∞)
  proof: by
  have hf : forall i, ((↑) : s -> Real>=0∞) i != ∞ := fun ⟨r, rs⟩ => hs r rs
  simpa only [← sSup_range, ← image_eq_range, Subtype.range_coe_subtype] using! (toNNReal_iSup hf)

中文:
定理 toNNReal_sSup
  条件: (s : Set 实数>=0∞) (hs : 对任意 r in s, r != ∞)
  证明: by
  have hf : forall i, ((↑) : s -> Real>=0∞) i != ∞ := fun ⟨r, rs⟩ => hs r rs
  simpa only [← sSup_range, ← image_eq_range, Subtype.range_coe_subtype] using! (toNNReal_iSup hf)

Depends on / 依赖: Subtype, Subtype.range_coe_subtype, image_eq_range, range_coe_subtype, sSup_range, toNNReal_iSup
-/
theorem toNNReal_sSup (s : Set Real>=0∞) (hs : forall r in s, r != ∞) :
    (sSup s).toNNReal = sSup (ENNReal.toNNReal '' s) := by
  have hf : forall i, ((↑) : s -> Real>=0∞) i != ∞ := fun ⟨r, rs⟩ => hs r rs
  simpa only [← sSup_range, ← image_eq_range, Subtype.range_coe_subtype] using! (toNNReal_iSup hf)

/--
theorem `toReal_iSup` / 定理 `toReal_iSup`

English:
theorem toReal_iSup
  given: (hf : forall i, f i != ∞)
  statement: (iSup f).toReal = ⨆ i, (f i).toReal
  proof: by
  simp only [ENNReal.toReal, toNNReal_iSup hf, NNReal.coe_iSup]

中文:
定理 toReal_iSup
  条件: (hf : 对任意 i, f i != ∞)
  结论: (iSup f).to实数 = ⨆ i, (f i).to实数
  证明: by
  simp only [ENNReal.toReal, toNNReal_iSup hf, NNReal.coe_iSup]

Depends on / 依赖: ENNReal, ENNReal.toReal, NNReal, NNReal.coe_iSup, coe_iSup, toNNReal_iSup, toReal
-/
theorem toReal_iSup (hf : forall i, f i != ∞) : (iSup f).toReal = ⨆ i, (f i).toReal := by
  simp only [ENNReal.toReal, toNNReal_iSup hf, NNReal.coe_iSup]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `toReal_sSup` / 定理 `toReal_sSup`

English:
theorem toReal_sSup
  given: (s : Set Real>=0∞) (hf : forall r in s, r != ∞)
  proof: by
  simp only [ENNReal.toReal, toNNReal_sSup s hf, NNReal.coe_sSup, Set.image_image]

中文:
定理 toReal_sSup
  条件: (s : Set 实数>=0∞) (hf : 对任意 r in s, r != ∞)
  证明: by
  simp only [ENNReal.toReal, toNNReal_sSup s hf, NNReal.coe_sSup, Set.image_image]

Depends on / 依赖: ENNReal, ENNReal.toReal, NNReal, NNReal.coe_sSup, Set.image_image, coe_sSup, image_image, toNNReal_sSup, toReal
-/
theorem toReal_sSup (s : Set Real>=0∞) (hf : forall r in s, r != ∞) :
    (sSup s).toReal = sSup (ENNReal.toReal '' s) := by
  simp only [ENNReal.toReal, toNNReal_sSup s hf, NNReal.coe_sSup, Set.image_image]

/--
theorem `iSup_sub` / 定理 `iSup_sub`

English:
theorem iSup_sub
  statement: (⨆ i, f i) - a = ⨆ i, f i - a
  proof: le_antisymm (tsub_le_iff_right.2 <| iSup_le fun i => tsub_le_iff_right.1 <| le_iSup (f · - a) i)
    (iSup_le fun _ => tsub_le_tsub (le_iSup _ _) (le_refl a))

中文:
定理 iSup_sub
  结论: (⨆ i, f i) - a = ⨆ i, f i - a
  证明: le_antisymm (tsub_le_iff_right.2 <| iSup_le fun i => tsub_le_iff_right.1 <| le_iSup (f · - a) i)
    (iSup_le fun _ => tsub_le_tsub (le_iSup _ _) (le_refl a))

Depends on / 依赖: iSup_le, le_antisymm, le_iSup, le_refl, tsub_le_iff_right, tsub_le_tsub
-/
theorem iSup_sub : (⨆ i, f i) - a = ⨆ i, f i - a :=
  le_antisymm (tsub_le_iff_right.2 <| iSup_le fun i => tsub_le_iff_right.1 <| le_iSup (f · - a) i)
    (iSup_le fun _ => tsub_le_tsub (le_iSup _ _) (le_refl a))

/--
lemma `iSup_eq_zero` / 引理 `iSup_eq_zero`

English:
lemma iSup_eq_zero
  statement: ⨆ i, f i = 0 ↔ forall i, f i = 0
  proof: iSup_eq_bot

中文:
引理 iSup_eq_zero
  结论: ⨆ i, f i = 0 ↔ 对任意 i, f i = 0
  证明: iSup_eq_bot
-/
@[simp] lemma iSup_eq_zero : ⨆ i, f i = 0 ↔ forall i, f i = 0 := iSup_eq_bot

/--
lemma `iSup_zero` / 引理 `iSup_zero`

English:
lemma iSup_zero
  statement: ⨆ _ : ι, (0 : Real>=0∞) = 0
  proof: by simp

中文:
引理 iSup_zero
  结论: ⨆ _ : ι, (0 : 实数>=0∞) = 0
  证明: by simp
-/
@[simp] lemma iSup_zero : ⨆ _ : ι, (0 : Real>=0∞) = 0 := by simp

/--
lemma `iSup_natCast` / 引理 `iSup_natCast`

English:
lemma iSup_natCast
  statement: ⨆ n : Nat, (n : Real>=0∞) = ∞
  proof: iSup_eq_top.2 fun _b hb => ENNReal.exists_nat_gt (lt_top_iff_ne_top.1 hb)

中文:
引理 iSup_natCast
  结论: ⨆ n : 自然数, (n : 实数>=0∞) = ∞
  证明: iSup_eq_top.2 fun _b hb => ENNReal.exists_nat_gt (lt_top_iff_ne_top.1 hb)

Depends on / 依赖: ENNReal, ENNReal.exists_nat_gt, exists_nat_gt, iSup_eq_top, lt_top_iff_ne_top
-/
lemma iSup_natCast : ⨆ n : Nat, (n : Real>=0∞) = ∞ :=
  iSup_eq_top.2 fun _b hb => ENNReal.exists_nat_gt (lt_top_iff_ne_top.1 hb)

/--
lemma `add_iSup` / 引理 `add_iSup`

English:
lemma add_iSup
  given: [Nonempty ι] (f : ι -> Real>=0∞)
  statement: a + ⨆ i, f i = ⨆ i, a + f i
  proof: by
  obtain rfl | ha := eq_or_ne a ∞
  · simp
refine le_antisymm ?_ iSup_le fun i => by grw [← le_iSup]
  refine add_le_of_le_tsub_left_of_le (le_iSup_of_le (Classical.arbitrary _) le_self_add) ?_
exact iSup_le fun i => ENNReal.le_sub_of_add_le_left ha le_iSup (a + f ·) i

中文:
引理 add_iSup
  条件: [Nonempty ι] (f : ι -> 实数>=0∞)
  结论: a + ⨆ i, f i = ⨆ i, a + f i
  证明: by
  obtain rfl | ha := eq_or_ne a ∞
  · simp
refine le_antisymm ?_ iSup_le fun i => by grw [← le_iSup]
  refine add_le_of_le_tsub_left_of_le (le_iSup_of_le (Classical.arbitrary _) le_self_add) ?_
exact iSup_le fun i => ENNReal.le_sub_of_add_le_left ha le_iSup (a + f ·) i

Depends on / 依赖: Classical, Classical.arbitrary, ENNReal, ENNReal.le_sub_of_add_le_left, add_le_of_le_tsub_left_of_le, arbitrary, eq_or_ne, iSup_le, le_antisymm, le_iSup, le_iSup_of_le, le_self_add, le_sub_of_add_le_left
-/
lemma add_iSup [Nonempty ι] (f : ι -> Real>=0∞) : a + ⨆ i, f i = ⨆ i, a + f i := by
  obtain rfl | ha := eq_or_ne a ∞
  · simp
refine le_antisymm ?_ iSup_le fun i => by grw [← le_iSup]
  refine add_le_of_le_tsub_left_of_le (le_iSup_of_le (Classical.arbitrary _) le_self_add) ?_
exact iSup_le fun i => ENNReal.le_sub_of_add_le_left ha le_iSup (a + f ·) i

/--
lemma `iSup_add` / 引理 `iSup_add`

English:
lemma iSup_add
  given: [Nonempty ι] (f : ι -> Real>=0∞)
  statement: (⨆ i, f i) + a = ⨆ i, f i + a
  proof: by
  simp [add_comm, add_iSup]

中文:
引理 iSup_add
  条件: [Nonempty ι] (f : ι -> 实数>=0∞)
  结论: (⨆ i, f i) + a = ⨆ i, f i + a
  证明: by
  simp [add_comm, add_iSup]

Depends on / 依赖: add_comm, add_iSup
-/
lemma iSup_add [Nonempty ι] (f : ι -> Real>=0∞) : (⨆ i, f i) + a = ⨆ i, f i + a := by
  simp [add_comm, add_iSup]

/--
lemma `add_biSup'` / 引理 `add_biSup'`

English:
lemma add_biSup'
  given: {p : ι -> Prop} (h : exists i, p i) (f : ι -> Real>=0∞)
  proof: by
  have : Nonempty {i // p i} := nonempty_subtype.2 h
  simp only [iSup_subtype', add_iSup]

中文:
引理 add_biSup'
  条件: {p : ι -> 命题} (h : 存在 i, p i) (f : ι -> 实数>=0∞)
  证明: by
  have : Nonempty {i // p i} := nonempty_subtype.2 h
  simp only [iSup_subtype', add_iSup]

Depends on / 依赖: Nonempty, add_iSup, iSup_subtype, nonempty_subtype
-/
lemma add_biSup' {p : ι -> Prop} (h : exists i, p i) (f : ι -> Real>=0∞) :
    a + ⨆ i, ⨆ _ : p i, f i = ⨆ i, ⨆ _ : p i, a + f i := by
  have : Nonempty {i // p i} := nonempty_subtype.2 h
  simp only [iSup_subtype', add_iSup]

/--
lemma `biSup_add'` / 引理 `biSup_add'`

English:
lemma biSup_add'
  given: {p : ι -> Prop} (h : exists i, p i) (f : ι -> Real>=0∞)
  proof: by simp only [add_comm, add_biSup' h]

中文:
引理 biSup_add'
  条件: {p : ι -> 命题} (h : 存在 i, p i) (f : ι -> 实数>=0∞)
  证明: by simp only [add_comm, add_biSup' h]

Depends on / 依赖: add_biSup, add_comm
-/
lemma biSup_add' {p : ι -> Prop} (h : exists i, p i) (f : ι -> Real>=0∞) :
    (⨆ i, ⨆ _ : p i, f i) + a = ⨆ i, ⨆ _ : p i, f i + a := by simp only [add_comm, add_biSup' h]

/--
lemma `add_biSup` / 引理 `add_biSup`

English:
lemma add_biSup
  given: {ι : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι -> Real>=0∞)
  proof: add_biSup' hs _

中文:
引理 add_biSup
  条件: {ι : 类型} {s : Set ι} (hs : s.Nonempty) (f : ι -> 实数>=0∞)
  证明: add_biSup' hs _

Depends on / 依赖: add_biSup
-/
lemma add_biSup {ι : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι -> Real>=0∞) :
    a + ⨆ i in s, f i = ⨆ i in s, a + f i := add_biSup' hs _

/--
lemma `biSup_add` / 引理 `biSup_add`

English:
lemma biSup_add
  given: {ι : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι -> Real>=0∞)
  proof: biSup_add' hs _

中文:
引理 biSup_add
  条件: {ι : 类型} {s : Set ι} (hs : s.Nonempty) (f : ι -> 实数>=0∞)
  证明: biSup_add' hs _

Depends on / 依赖: biSup_add
-/
lemma biSup_add {ι : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι -> Real>=0∞) :
    (⨆ i in s, f i) + a = ⨆ i in s, f i + a := biSup_add' hs _

/--
lemma `add_sSup` / 引理 `add_sSup`

English:
lemma add_sSup
  given: (hs : s.Nonempty)
  statement: a + sSup s = ⨆ b in s, a + b
  proof: by
  rw [sSup_eq_iSup]; rw [add_biSup hs]

中文:
引理 add_sSup
  条件: (hs : s.Nonempty)
  结论: a + sSup s = ⨆ b in s, a + b
  证明: by
  rw [sSup_eq_iSup]; rw [add_biSup hs]

Depends on / 依赖: add_biSup, sSup_eq_iSup
-/
lemma add_sSup (hs : s.Nonempty) : a + sSup s = ⨆ b in s, a + b := by
  rw [sSup_eq_iSup]; rw [add_biSup hs]

/--
lemma `sSup_add` / 引理 `sSup_add`

English:
lemma sSup_add
  given: (hs : s.Nonempty)
  statement: sSup s + a = ⨆ b in s, b + a
  proof: by
  rw [sSup_eq_iSup]; rw [biSup_add hs]

中文:
引理 sSup_add
  条件: (hs : s.Nonempty)
  结论: sSup s + a = ⨆ b in s, b + a
  证明: by
  rw [sSup_eq_iSup]; rw [biSup_add hs]

Depends on / 依赖: biSup_add, sSup_eq_iSup
-/
lemma sSup_add (hs : s.Nonempty) : sSup s + a = ⨆ b in s, b + a := by
  rw [sSup_eq_iSup]; rw [biSup_add hs]

/--
lemma `iSup_add_iSup_le` / 引理 `iSup_add_iSup_le`

English:
lemma iSup_add_iSup_le
  given: [Nonempty ι] [Nonempty κ] {g : κ -> Real>=0∞} (h : forall i j, f i + g j <= a)
  proof: by simp_rw [iSup_add, add_iSup]; exact iSup₂_le h

中文:
引理 iSup_add_iSup_le
  条件: [Nonempty ι] [Nonempty κ] {g : κ -> 实数>=0∞} (h : 对任意 i j, f i + g j <= a)
  证明: by simp_rw [iSup_add, add_iSup]; exact iSup₂_le h

Depends on / 依赖: add_iSup, iSup_add, simp_rw
-/
lemma iSup_add_iSup_le [Nonempty ι] [Nonempty κ] {g : κ -> Real>=0∞} (h : forall i j, f i + g j <= a) :
    iSup f + iSup g <= a := by simp_rw [iSup_add, add_iSup]; exact iSup₂_le h

/--
lemma `biSup_add_biSup_le'` / 引理 `biSup_add_biSup_le'`

English:
lemma biSup_add_biSup_le'
  statement: {p : ι -> Prop} {q : κ -> Prop} (hp : exists i, p i) (hq : exists j, q j)
  proof: by
  simp_rw [biSup_add' hp, add_biSup' hq]
  exact iSup₂_le fun i hi => iSup₂_le (h i hi)

中文:
引理 biSup_add_biSup_le'
  结论: {p : ι -> 命题} {q : κ -> 命题} (hp : 存在 i, p i) (hq : 存在 j, q j)
  证明: by
  simp_rw [biSup_add' hp, add_biSup' hq]
  exact iSup₂_le fun i hi => iSup₂_le (h i hi)

Depends on / 依赖: add_biSup, biSup_add, simp_rw
-/
lemma biSup_add_biSup_le' {p : ι -> Prop} {q : κ -> Prop} (hp : exists i, p i) (hq : exists j, q j)
    {g : κ -> Real>=0∞} (h : forall i, p i -> forall j, q j -> f i + g j <= a) :
    (⨆ i, ⨆ _ : p i, f i) + ⨆ j, ⨆ _ : q j, g j <= a := by
  simp_rw [biSup_add' hp, add_biSup' hq]
  exact iSup₂_le fun i hi => iSup₂_le (h i hi)

/--
lemma `biSup_add_biSup_le` / 引理 `biSup_add_biSup_le`

English:
lemma biSup_add_biSup_le
  statement: {ι κ : Type*} {s : Set ι} {t : Set κ} (hs : s.Nonempty) (ht : t.Nonempty)
  proof: biSup_add_biSup_le' hs ht h

中文:
引理 biSup_add_biSup_le
  结论: {ι κ : 类型} {s : Set ι} {t : Set κ} (hs : s.Nonempty) (ht : t.Nonempty)
  证明: biSup_add_biSup_le' hs ht h

Depends on / 依赖: biSup_add_biSup_le
-/
lemma biSup_add_biSup_le {ι κ : Type*} {s : Set ι} {t : Set κ} (hs : s.Nonempty) (ht : t.Nonempty)
    {f : ι -> Real>=0∞} {g : κ -> Real>=0∞} {a : Real>=0∞} (h : forall i in s, forall j in t, f i + g j <= a) :
    (⨆ i in s, f i) + ⨆ j in t, g j <= a := biSup_add_biSup_le' hs ht h

/--
lemma `iSup_add_iSup` / 引理 `iSup_add_iSup`

English:
lemma iSup_add_iSup
  given: (h : forall i j, exists k, f i + g j <= f k + g k)
  statement: iSup f + iSup g = ⨆ i, f i + g i
  proof: by
  cases isEmpty_or_nonempty ι
  · simp
  · refine le_antisymm ?_ (iSup_le fun a => add_le_add (le_iSup _ _) (le_iSup _ _))
    refine iSup_add_iSup_le fun i j => ?_
    rcases h i j with ⟨k, hk⟩
    exact le_iSup_of_le k hk

中文:
引理 iSup_add_iSup
  条件: (h : 对任意 i j, 存在 k, f i + g j <= f k + g k)
  结论: iSup f + iSup g = ⨆ i, f i + g i
  证明: by
  cases isEmpty_or_nonempty ι
  · simp
  · refine le_antisymm ?_ (iSup_le fun a => add_le_add (le_iSup _ _) (le_iSup _ _))
    refine iSup_add_iSup_le fun i j => ?_
    rcases h i j with ⟨k, hk⟩
    exact le_iSup_of_le k hk

Depends on / 依赖: add_le_add, iSup_add_iSup_le, iSup_le, isEmpty_or_nonempty, le_antisymm, le_iSup, le_iSup_of_le
-/
lemma iSup_add_iSup (h : forall i j, exists k, f i + g j <= f k + g k) : iSup f + iSup g = ⨆ i, f i + g i := by
  cases isEmpty_or_nonempty ι
  · simp
  · refine le_antisymm ?_ (iSup_le fun a => add_le_add (le_iSup _ _) (le_iSup _ _))
    refine iSup_add_iSup_le fun i j => ?_
    rcases h i j with ⟨k, hk⟩
    exact le_iSup_of_le k hk

/--
lemma `iSup_add_iSup_of_monotone` / 引理 `iSup_add_iSup_of_monotone`

English:
lemma iSup_add_iSup_of_monotone
  statement: {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {f g : ι -> Real>=0∞}
  proof: iSup_add_iSup fun i j => (exists_ge_ge i j).imp fun _k ⟨hi, hj⟩ => by gcongr <;> apply_rules

中文:
引理 iSup_add_iSup_of_monotone
  结论: {ι : 类型} [Preorder ι] [IsDirectedOrder ι] {f g : ι -> 实数>=0∞}
  证明: iSup_add_iSup fun i j => (exists_ge_ge i j).imp fun _k ⟨hi, hj⟩ => by gcongr <;> apply_rules

Depends on / 依赖: apply_rules, exists_ge_ge, iSup_add_iSup
-/
lemma iSup_add_iSup_of_monotone {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {f g : ι -> Real>=0∞}
    (hf : Monotone f) (hg : Monotone g) : iSup f + iSup g = ⨆ a, f a + g a :=
  iSup_add_iSup fun i j => (exists_ge_ge i j).imp fun _k ⟨hi, hj⟩ => by gcongr <;> apply_rules

/--
lemma `sub_iSup` / 引理 `sub_iSup`

English:
lemma sub_iSup
  given: [Nonempty ι] (ha : a != ∞)
  statement: a - ⨆ i, f i = ⨅ i, a - f i
  proof: by
  obtain ⟨i, hi⟩ | h := em (exists i, a < f i)
  · rw [tsub_eq_zero_iff_le.2 <| le_iSup_of_le _ hi.le, iInf_eq_bot.2, bot_eq_zero]
    exact fun x hx => ⟨i, by simpa [hi.le, tsub_eq_zero_of_le]⟩
  simp_rw [not_exists, not_lt] at h
refine le_antisymm (le_iInf fun i => tsub_le_tsub_left (le_iSup ..

中文:
引理 sub_iSup
  条件: [Nonempty ι] (ha : a != ∞)
  结论: a - ⨆ i, f i = ⨅ i, a - f i
  证明: by
  obtain ⟨i, hi⟩ | h := em (exists i, a < f i)
  · rw [tsub_eq_zero_iff_le.2 <| le_iSup_of_le _ hi.le, iInf_eq_bot.2, bot_eq_zero]
    exact fun x hx => ⟨i, by simpa [hi.le, tsub_eq_zero_of_le]⟩
  simp_rw [not_exists, not_lt] at h
refine le_antisymm (le_iInf fun i => tsub_le_tsub_left (le_iSup ..

Depends on / 依赖: Classical, Classical.arbitrary, ENNReal, ENNReal.le_sub_of_add_le_left, add_le_of_le_tsub_right_of_le, arbitrary, bot_eq_zero, hi.le, iInf_eq_bot, iInf_le_of_le, iSup_le, le_antisymm, le_iInf, le_iSup, le_iSup_of_le, le_sub_of_add_le_left, ne_top_of_le_ne_top, not_exists, not_lt, simp_rw
-/
lemma sub_iSup [Nonempty ι] (ha : a != ∞) : a - ⨆ i, f i = ⨅ i, a - f i := by
  obtain ⟨i, hi⟩ | h := em (exists i, a < f i)
  · rw [tsub_eq_zero_iff_le.2 <| le_iSup_of_le _ hi.le, iInf_eq_bot.2, bot_eq_zero]
    exact fun x hx => ⟨i, by simpa [hi.le, tsub_eq_zero_of_le]⟩
  simp_rw [not_exists, not_lt] at h
refine le_antisymm (le_iInf fun i => tsub_le_tsub_left (le_iSup ..) _)
ENNReal.le_sub_of_add_le_left (ne_top_of_le_ne_top ha <| iSup_le h)
add_le_of_le_tsub_right_of_le (iInf_le_of_le (Classical.arbitrary _) tsub_le_self)
    iSup_le fun i => ?_
  rw [← sub_sub_cancel ha (h _)]
  exact tsub_le_tsub_left (iInf_le (a - f ·) i) _

/--
lemma `iSup_lt_eq_self` / 引理 `iSup_lt_eq_self`

English:
lemma iSup_lt_eq_self
  given: (a : Real>=0∞)
  statement: ⨆ b, ⨆ _ : b < a, b = a
  proof: by
  refine le_antisymm (iSup₂_le fun b hb => hb.le) ?_
  refine le_of_forall_lt fun c hca => ?_
  obtain ⟨d, hcd, hdb⟩ := exists_between hca
exact hcd.trans_le le_iSup₂_of_le d hdb le_rfl

中文:
引理 iSup_lt_eq_self
  条件: (a : 实数>=0∞)
  结论: ⨆ b, ⨆ _ : b < a, b = a
  证明: by
  refine le_antisymm (iSup₂_le fun b hb => hb.le) ?_
  refine le_of_forall_lt fun c hca => ?_
  obtain ⟨d, hcd, hdb⟩ := exists_between hca
exact hcd.trans_le le_iSup₂_of_le d hdb le_rfl
-/
@[simp] lemma iSup_lt_eq_self (a : Real>=0∞) : ⨆ b, ⨆ _ : b < a, b = a := by
  refine le_antisymm (iSup₂_le fun b hb => hb.le) ?_
  refine le_of_forall_lt fun c hca => ?_
  obtain ⟨d, hcd, hdb⟩ := exists_between hca
exact hcd.trans_le le_iSup₂_of_le d hdb le_rfl

-- TODO: Prove the two one-side versions
/--
lemma `exists_lt_add_of_lt_add` / 引理 `exists_lt_add_of_lt_add`

English:
lemma exists_lt_add_of_lt_add
  given: {x y z : Real>=0∞} (h : x < y + z) (hy : y != 0) (hz : z != 0)
  proof: by
  contrapose! h
  simpa using biSup_add_biSup_le' (by exact ⟨0, hy.bot_lt⟩) (by exact ⟨0, hz.bot_lt⟩) h

中文:
引理 exists_lt_add_of_lt_add
  条件: {x y z : 实数>=0∞} (h : x < y + z) (hy : y != 0) (hz : z != 0)
  证明: by
  contrapose! h
  simpa using biSup_add_biSup_le' (by exact ⟨0, hy.bot_lt⟩) (by exact ⟨0, hz.bot_lt⟩) h

Depends on / 依赖: biSup_add_biSup_le, bot_lt, contrapose, hy.bot_lt, hz.bot_lt
-/
lemma exists_lt_add_of_lt_add {x y z : Real>=0∞} (h : x < y + z) (hy : y != 0) (hz : z != 0) :
    exists y' < y, exists z' < z, x < y' + z' := by
  contrapose! h
  simpa using biSup_add_biSup_le' (by exact ⟨0, hy.bot_lt⟩) (by exact ⟨0, hz.bot_lt⟩) h

end iSup

end ENNReal
