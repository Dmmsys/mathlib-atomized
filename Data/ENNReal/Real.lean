/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Data.ENNReal.Basic

/-!
# Maps between real and extended non-negative real numbers

This file focuses on the functions `ENNReal.toReal : ℝ≥0∞ → ℝ` and `ENNReal.ofReal : ℝ → ℝ≥0∞` which
were defined in `Data.ENNReal.Basic`. It collects all the basic results of the interactions between
these functions and the algebraic and lattice operations, although a few may appear in earlier
files.

This file provides a `positivity` extension for `ENNReal.ofReal`.

## Main statements

  - `trichotomy (p : ℝ≥0∞) : p = 0 ∨ p = ∞ ∨ 0 < p.toReal`: often used for `WithLp` and `lp`
  - `dichotomy (p : ℝ≥0∞) [Fact (1 ≤ p)] : p = ∞ ∨ 1 ≤ p.toReal`: often used for `WithLp` and `lp`
  - `toNNReal_iInf` through `toReal_sSup`: these declarations allow for easy conversions between
    indexed or set infima and suprema in `ℝ`, `ℝ≥0` and `ℝ≥0∞`. This is especially useful because
    `ℝ≥0∞` is a complete lattice.
-/

@[expose] public section

assert_not_exists Finset

open Set NNReal ENNReal

namespace ENNReal

section Real

variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

/-
**ENNReal.toReal_add** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_add (ha : a != ∞) (hb : b != ∞) : (a + b).toReal = a.toReal + b.toR
eal
参数：ha : a != ∞；hb : b != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
-/
theorem toReal_add (ha : a ≠ ∞) (hb : b ≠ ∞) : (a + b).toReal = a.toReal + b.toReal := by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  rfl
/-
**ENNReal.toReal_add_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_add_le : (a + b).toReal <= a.toReal + b.toReal
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `ENNReal.toReal_add`：toReal_add (ha : a != ∞) (hb : b != ∞) : (a + b).toR
eal = a.toReal + b.toReal
-/
theorem toReal_add_le : (a + b).toReal ≤ a.toReal + b.toReal :=
  if ha : a = ∞ then by simp only [ha, top_add, toReal_top, zero_add, toReal_nonneg]
  else
    if hb : b = ∞ then by simp only [hb, add_top, toReal_top, add_zero, toReal_nonneg]
    else le_of_eq (toReal_add ha hb)
/-
**ENNReal.ofReal_add** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_add {p q : Real} (hp : 0 <= p) (hq : 0 <= q) : ENNReal.ofReal (p + 
q) = ENNReal.ofReal p + ENNReal.ofReal q
参数：hp : 0 <= p；hq : 0 <= q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal.eq_1`：∀ (r : ℝ), ENNReal.ofReal r = ↑r.toNNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_add`：∀ (x y : NNReal), ↑(x + y) = ↑x + ↑y
· 使用定理 `ENNReal.coe_inj`：∀ {p q : NNReal}, ↑p = ↑q ↔ p = q
· 使用定理 `Real.toNNReal_add`：toNNReal_add {r p : Real} (hr : 0 <= r) (hp : 0 <= p)
 : Real.toNNReal (r + p) = Real.toNNReal r + Real.toNNReal p
-/
theorem ofReal_add {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ENNReal.ofReal (p + q) = ENNReal.ofReal p + ENNReal.ofReal q := by
  rw [ENNReal.ofReal, ENNReal.ofReal, ENNReal.ofReal, ← coe_add, coe_inj,
    Real.toNNReal_add hp hq]
/-
**ENNReal.ofReal_add_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_add_le {p q : Real} : ENNReal.ofReal (p + q) <= ENNReal.ofReal p + 
ENNReal.ofReal q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `Real.toNNReal_add_le`：toNNReal_add_le {r p : Real} : Real.toNNReal (r + 
p) <= Real.toNNReal r + Real.toNNReal p
-/
theorem ofReal_add_le {p q : ℝ} : ENNReal.ofReal (p + q) ≤ ENNReal.ofReal p + ENNReal.ofReal q :=
  coe_le_coe.2 Real.toNNReal_add_le

@[simp]
/-
**ENNReal.toReal_le_toReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_le_toReal (ha : a != ∞) (hb : b != ∞) : a.toReal <= b.toReal ↔ a <=
 b
参数：ha : a != ∞；hb : b != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toReal_le_toReal (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toReal ≤ b.toReal ↔ a ≤ b := by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  norm_cast

@[gcongr]
/-
**ENNReal.toReal_mono** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <= b.toReal
参数：hb : b != ∞；h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.toReal_le_toReal`：toReal_le_toReal (ha : a != ∞) (hb : b != ∞) :
 a.toReal <= b.toReal ↔ a <= b
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
-/
theorem toReal_mono (hb : b ≠ ∞) (h : a ≤ b) : a.toReal ≤ b.toReal :=
  (toReal_le_toReal (ne_top_of_le_ne_top hb h) hb).2 h
/-
**ENNReal.toReal_mono'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_mono' (h : a <= b) (ht : b = ∞ -> a = ∞) : a.toReal <= b.toReal
参数：h : a <= b；ht : b = ∞ -> a = ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
-/
theorem toReal_mono' (h : a ≤ b) (ht : b = ∞ → a = ∞) : a.toReal ≤ b.toReal := by
  rcases eq_or_ne a ∞ with rfl | ha
  · exact toReal_nonneg
  · exact toReal_mono (mt ht ha) h

@[simp]
/-
**ENNReal.toReal_lt_toReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_lt_toReal (ha : a != ∞) (hb : b != ∞) : a.toReal < b.toReal ↔ a < b
参数：ha : a != ∞；hb : b != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toReal_lt_toReal (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toReal < b.toReal ↔ a < b := by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  norm_cast

@[gcongr]
/-
**ENNReal.toReal_strict_mono** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_strict_mono (hb : b != ∞) (h : a < b) : a.toReal < b.toReal
参数：hb : b != ∞；h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.toReal_lt_toReal`：toReal_lt_toReal (ha : a != ∞) (hb : b != ∞) :
 a.toReal < b.toReal ↔ a < b
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
-/
theorem toReal_strict_mono (hb : b ≠ ∞) (h : a < b) : a.toReal < b.toReal :=
  (toReal_lt_toReal h.ne_top hb).2 h

@[gcongr]
/-
**ENNReal.toNNReal_mono** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toNNReal_mono (hb : b != ∞) (h : a <= b) : a.toNNReal <= b.toNNReal
参数：hb : b != ∞；h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
-/
theorem toNNReal_mono (hb : b ≠ ∞) (h : a ≤ b) : a.toNNReal ≤ b.toNNReal :=
  toReal_mono hb h
/-
**ENNReal.le_toNNReal_of_coe_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：le_toNNReal_of_coe_le (h : p <= a) (ha : a != ∞) : p <= a.toNNReal
参数：h : p <= a；ha : a != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toNNReal_mono`：toNNReal_mono (hb : b != ∞) (h : a <= b) : a.toNN
Real <= b.toNNReal
· 使用定理 `ENNReal.toNNReal_coe`：∀ (r : NNReal), (↑r).toNNReal = r
-/
theorem le_toNNReal_of_coe_le (h : p ≤ a) (ha : a ≠ ∞) : p ≤ a.toNNReal :=
  @toNNReal_coe p ▸ toNNReal_mono ha h

@[simp]
/-
**ENNReal.toNNReal_le_toNNReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toNNReal_le_toNNReal (ha : a != ∞) (hb : b != ∞) : a.toNNReal <= b.toNNRea
l ↔ a <= b
参数：ha : a != ∞；hb : b != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `ENNReal.toNNReal_mono`：toNNReal_mono (hb : b != ∞) (h : a <= b) : a.toNN
Real <= b.toNNReal
-/
theorem toNNReal_le_toNNReal (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toNNReal ≤ b.toNNReal ↔ a ≤ b :=
  ⟨fun h => by rwa [← coe_toNNReal ha, ← coe_toNNReal hb, coe_le_coe], toNNReal_mono hb⟩

@[gcongr]
/-
**ENNReal.toNNReal_strict_mono** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toNNReal_strict_mono (hb : b != ∞) (h : a < b) : a.toNNReal < b.toNNReal
参数：hb : b != ∞；h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem toNNReal_strict_mono (hb : b ≠ ∞) (h : a < b) : a.toNNReal < b.toNNReal := by
  simpa [← ENNReal.coe_lt_coe, hb, h.ne_top]

@[simp]
/-
**ENNReal.toNNReal_lt_toNNReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toNNReal_lt_toNNReal (ha : a != ∞) (hb : b != ∞) : a.toNNReal < b.toNNReal
 ↔ a < b
参数：ha : a != ∞；hb : b != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
· 使用定理 `ENNReal.toNNReal_strict_mono`：toNNReal_strict_mono (hb : b != ∞) (h : a 
< b) : a.toNNReal < b.toNNReal
-/
theorem toNNReal_lt_toNNReal (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toNNReal < b.toNNReal ↔ a < b :=
  ⟨fun h => by rwa [← coe_toNNReal ha, ← coe_toNNReal hb, coe_lt_coe], toNNReal_strict_mono hb⟩
/-
**ENNReal.toNNReal_lt_of_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toNNReal_lt_of_lt_coe (h : a < p) : a.toNNReal < p
参数：h : a < p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toNNReal_strict_mono`：toNNReal_strict_mono (hb : b != ∞) (h : a 
< b) : a.toNNReal < b.toNNReal
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `ENNReal.toNNReal_coe`：∀ (r : NNReal), (↑r).toNNReal = r
-/
theorem toNNReal_lt_of_lt_coe (h : a < p) : a.toNNReal < p :=
  @toNNReal_coe p ▸ toNNReal_strict_mono coe_ne_top h
/-
**ENNReal.toReal_max** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_max (hr : a != ∞) (hp : b != ∞) : ENNReal.toReal (max a b) = max (E
NNReal.toReal a) (ENNReal.toReal b)
参数：hr : a != ∞；hp : b != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
-/
theorem toReal_max (hr : a ≠ ∞) (hp : b ≠ ∞) :
    ENNReal.toReal (max a b) = max (ENNReal.toReal a) (ENNReal.toReal b) :=
  (le_total a b).elim
    (fun h => by simp only [h, ENNReal.toReal_mono hp h, max_eq_right]) fun h => by
    simp only [h, ENNReal.toReal_mono hr h, max_eq_left]
/-
**ENNReal.toReal_min** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_min {a b : Real>=0∞} (hr : a != ∞) (hp : b != ∞) : ENNReal.toReal (
min a b) = min (ENNReal.toReal a) (ENNReal.toReal b)
参数：hr : a != ∞；hp : b != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
-/
theorem toReal_min {a b : ℝ≥0∞} (hr : a ≠ ∞) (hp : b ≠ ∞) :
    ENNReal.toReal (min a b) = min (ENNReal.toReal a) (ENNReal.toReal b) :=
  (le_total a b).elim (fun h => by simp only [h, ENNReal.toReal_mono hp h, min_eq_left])
    fun h => by simp only [h, ENNReal.toReal_mono hr h, min_eq_right]
/-
**ENNReal.toReal_sup** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_sup {a b : Real>=0∞} : a != ∞ -> b != ∞ -> (a ⊔ b).toReal = a.toRea
l ⊔ b.toReal
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toReal_max`：toReal_max (hr : a != ∞) (hp : b != ∞) : ENNReal.toR
eal (max a b) = max (ENNReal.toReal a) (ENNReal.toReal b)
-/
theorem toReal_sup {a b : ℝ≥0∞} : a ≠ ∞ → b ≠ ∞ → (a ⊔ b).toReal = a.toReal ⊔ b.toReal :=
  toReal_max
/-
**ENNReal.toReal_inf** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_inf {a b : Real>=0∞} : a != ∞ -> b != ∞ -> (a ⊓ b).toReal = a.toRea
l ⊓ b.toReal
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toReal_min`：toReal_min {a b : Real>=0∞} (hr : a != ∞) (hp : b !=
 ∞) : ENNReal.toReal (min a b) = min (ENNReal.toReal a) (ENNReal.toReal b)
-/
theorem toReal_inf {a b : ℝ≥0∞} : a ≠ ∞ → b ≠ ∞ → (a ⊓ b).toReal = a.toReal ⊓ b.toReal :=
  toReal_min
/-
**ENNReal.toNNReal_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toNNReal_pos_iff : 0 < a.toNNReal ↔ 0 < a ∧ a < ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem toNNReal_pos_iff : 0 < a.toNNReal ↔ 0 < a ∧ a < ∞ := by
  induction a <;> simp
/-
**ENNReal.toNNReal_pos** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toNNReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a != ∞) : 0 < a.toNNR
eal
参数：ha₀ : a != 0；ha_top : a != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.toNNReal_pos_iff`：toNNReal_pos_iff : 0 < a.toNNReal ↔ 0 < a ∧ a 
< ∞
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
-/
theorem toNNReal_pos {a : ℝ≥0∞} (ha₀ : a ≠ 0) (ha_top : a ≠ ∞) : 0 < a.toNNReal :=
  toNNReal_pos_iff.mpr ⟨bot_lt_iff_ne_bot.mpr ha₀, lt_top_iff_ne_top.mpr ha_top⟩
/-
**ENNReal.toReal_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_pos_iff : 0 < a.toReal ↔ 0 < a ∧ a < ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `NNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `ENNReal.toNNReal_pos_iff`：toNNReal_pos_iff : 0 < a.toNNReal ↔ 0 < a ∧ a 
< ∞
-/
theorem toReal_pos_iff : 0 < a.toReal ↔ 0 < a ∧ a < ∞ :=
  NNReal.coe_pos.trans toNNReal_pos_iff
/-
**ENNReal.toReal_pos** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a != ∞) : 0 < a.toReal
参数：ha₀ : a != 0；ha_top : a != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.toReal_pos_iff`：toReal_pos_iff : 0 < a.toReal ↔ 0 < a ∧ a < ∞
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
-/
theorem toReal_pos {a : ℝ≥0∞} (ha₀ : a ≠ 0) (ha_top : a ≠ ∞) : 0 < a.toReal :=
  toReal_pos_iff.mpr ⟨bot_lt_iff_ne_bot.mpr ha₀, lt_top_iff_ne_top.mpr ha_top⟩

@[gcongr, bound]
/-
**ENNReal.ofReal_le_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_le_ofReal {p q : Real} (h : p <= q) : ENNReal.ofReal p <= ENNReal.o
fReal q
参数：h : p <= q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Real.toNNReal_le_toNNReal`：toNNReal_le_toNNReal {r p : Real} (h : r <= p
) : Real.toNNReal r <= Real.toNNReal p
-/
theorem ofReal_le_ofReal {p q : ℝ} (h : p ≤ q) : ENNReal.ofReal p ≤ ENNReal.ofReal q := by
  simp [ENNReal.ofReal, Real.toNNReal_le_toNNReal h]
/-
**ENNReal.ofReal_mono** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_mono : Monotone ENNReal.ofReal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
-/
lemma ofReal_mono : Monotone ENNReal.ofReal := fun _ _ ↦ ENNReal.ofReal_le_ofReal
/-
**ENNReal.ofReal_le_of_le_toReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_le_of_le_toReal {a : Real} {b : Real>=0∞} (h : a <= ENNReal.toReal 
b) : ENNReal.ofReal a <= b
参数：h : a <= ENNReal.toReal b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
· 使用定理 `ENNReal.ofReal_toReal_le`：ofReal_toReal_le {a : Real>=0∞} : ENNReal.ofRe
al a.toReal <= a
-/
theorem ofReal_le_of_le_toReal {a : ℝ} {b : ℝ≥0∞} (h : a ≤ ENNReal.toReal b) :
    ENNReal.ofReal a ≤ b :=
  (ofReal_le_ofReal h).trans ofReal_toReal_le

@[simp]
/-
**ENNReal.ofReal_le_ofReal_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_le_ofReal_iff {p q : Real} (h : 0 <= q) : ENNReal.ofReal p <= ENNRe
al.ofReal q ↔ p <= q
参数：h : 0 <= q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal.eq_1`：∀ (r : ℝ), ENNReal.ofReal r = ↑r.toNNReal
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `Real.toNNReal_le_toNNReal_iff`：toNNReal_le_toNNReal_iff {r p : Real} (hp
 : 0 <= p) : toNNReal r <= toNNReal p ↔ r <= p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofReal_le_ofReal_iff {p q : ℝ} (h : 0 ≤ q) :
    ENNReal.ofReal p ≤ ENNReal.ofReal q ↔ p ≤ q := by
  rw [ENNReal.ofReal, ENNReal.ofReal, coe_le_coe, Real.toNNReal_le_toNNReal_iff h]
/-
**ENNReal.ofReal_le_ofReal_iff'** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_le_ofReal_iff' {p q : Real} : ENNReal.ofReal p <= .ofReal q ↔ p <= 
q ∨ p <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用引理 `Real.toNNReal_le_toNNReal_iff'`：toNNReal_le_toNNReal_iff' {r p : Real} :
 r.toNNReal <= p.toNNReal ↔ r <= p ∨ r <= 0
-/
lemma ofReal_le_ofReal_iff' {p q : ℝ} : ENNReal.ofReal p ≤ .ofReal q ↔ p ≤ q ∨ p ≤ 0 :=
  coe_le_coe.trans Real.toNNReal_le_toNNReal_iff'

@[simp, norm_cast]
/-
**ENNReal.ofReal_le_coe** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_le_coe {a : Real} {b : Real>=0} : ENNReal.ofReal a <= b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `ENNReal.ofReal_coe_nnreal`：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ofReal_le_coe {a : ℝ} {b : ℝ≥0} : ENNReal.ofReal a ≤ b ↔ a ≤ b := by
  simp [← ofReal_le_ofReal_iff]
/-
**ENNReal.ofReal_lt_ofReal_iff'** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_lt_ofReal_iff' {p q : Real} : ENNReal.ofReal p < .ofReal q ↔ p < q 
∧ 0 < q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
· 使用定理 `Real.toNNReal_lt_toNNReal_iff'`：toNNReal_lt_toNNReal_iff' {r p : Real} :
 Real.toNNReal r < Real.toNNReal p ↔ r < p ∧ 0 < p
-/
lemma ofReal_lt_ofReal_iff' {p q : ℝ} : ENNReal.ofReal p < .ofReal q ↔ p < q ∧ 0 < q :=
  coe_lt_coe.trans Real.toNNReal_lt_toNNReal_iff'

@[simp]
/-
**ENNReal.ofReal_eq_ofReal_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_eq_ofReal_iff {p q : Real} (hp : 0 <= p) (hq : 0 <= q) : ENNReal.of
Real p = ENNReal.ofReal q ↔ p = q
参数：hp : 0 <= p；hq : 0 <= q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal.eq_1`：∀ (r : ℝ), ENNReal.ofReal r = ↑r.toNNReal
· 使用定理 `ENNReal.coe_inj`：∀ {p q : NNReal}, ↑p = ↑q ↔ p = q
· 使用定理 `Real.toNNReal_eq_toNNReal_iff`：toNNReal_eq_toNNReal_iff {r p : Real} (hr
 : 0 <= r) (hp : 0 <= p) : toNNReal r = toNNReal p ↔ r = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofReal_eq_ofReal_iff {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ENNReal.ofReal p = ENNReal.ofReal q ↔ p = q := by
  rw [ENNReal.ofReal, ENNReal.ofReal, coe_inj, Real.toNNReal_eq_toNNReal_iff hp hq]

@[simp]
/-
**ENNReal.ofReal_lt_ofReal_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_lt_ofReal_iff {p q : Real} (h : 0 < q) : ENNReal.ofReal p < ENNReal
.ofReal q ↔ p < q
参数：h : 0 < q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal.eq_1`：∀ (r : ℝ), ENNReal.ofReal r = ↑r.toNNReal
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
· 使用定理 `Real.toNNReal_lt_toNNReal_iff`：toNNReal_lt_toNNReal_iff {r p : Real} (h 
: 0 < p) : Real.toNNReal r < Real.toNNReal p ↔ r < p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofReal_lt_ofReal_iff {p q : ℝ} (h : 0 < q) :
    ENNReal.ofReal p < ENNReal.ofReal q ↔ p < q := by
  rw [ENNReal.ofReal, ENNReal.ofReal, coe_lt_coe, Real.toNNReal_lt_toNNReal_iff h]
/-
**ENNReal.ofReal_lt_ofReal_iff_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_lt_ofReal_iff_of_nonneg {p q : Real} (hp : 0 <= p) : ENNReal.ofReal
 p < ENNReal.ofReal q ↔ p < q
参数：hp : 0 <= p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal.eq_1`：∀ (r : ℝ), ENNReal.ofReal r = ↑r.toNNReal
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
· 使用定理 `Real.toNNReal_lt_toNNReal_iff_of_nonneg`：toNNReal_lt_toNNReal_iff_of_non
neg {r p : Real} (hr : 0 <= r) : Real.toNNReal r < Real.toNNReal p ↔ r < p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofReal_lt_ofReal_iff_of_nonneg {p q : ℝ} (hp : 0 ≤ p) :
    ENNReal.ofReal p < ENNReal.ofReal q ↔ p < q := by
  rw [ENNReal.ofReal, ENNReal.ofReal, coe_lt_coe, Real.toNNReal_lt_toNNReal_iff_of_nonneg hp]

@[simp]
/-
**ENNReal.ofReal_pos** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_pos {p : Real} : 0 < ENNReal.ofReal p ↔ 0 < p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ofReal_pos {p : ℝ} : 0 < ENNReal.ofReal p ↔ 0 < p := by simp [ENNReal.ofReal]

@[bound] private alias ⟨_, Bound.ofReal_pos_of_pos⟩ := ofReal_pos

@[simp]
/-
**ENNReal.ofReal_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_eq_zero {p : Real} : ENNReal.ofReal p = 0 ↔ p <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ofReal_eq_zero {p : ℝ} : ENNReal.ofReal p = 0 ↔ p ≤ 0 := by simp [ENNReal.ofReal]
/-
**ENNReal.ofReal_min** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (x y : ℝ), ENNReal.ofReal (min x y) = min (ENNReal.ofReal x) (ENNReal.of
Real y)
参数：x y : ℝ；min x y；ENNReal.ofReal x；ENNReal.ofReal y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用引理 `ENNReal.ofReal_mono`：ofReal_mono : Monotone ENNReal.ofReal
-/
@[simp] lemma ofReal_min (x y : ℝ) : ENNReal.ofReal (min x y) = min (.ofReal x) (.ofReal y) :=
  ofReal_mono.map_min
/-
**ENNReal.ofReal_max** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (x y : ℝ), ENNReal.ofReal (max x y) = max (ENNReal.ofReal x) (ENNReal.of
Real y)
参数：x y : ℝ；max x y；ENNReal.ofReal x；ENNReal.ofReal y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用引理 `ENNReal.ofReal_mono`：ofReal_mono : Monotone ENNReal.ofReal
-/
@[simp] lemma ofReal_max (x y : ℝ) : ENNReal.ofReal (max x y) = max (.ofReal x) (.ofReal y) :=
  ofReal_mono.map_max
/-
**ENNReal.ofReal_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_ne_zero_iff {r : Real} : ENNReal.ofReal r != 0 ↔ 0 < r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.ofReal_pos`：ofReal_pos {p : Real} : 0 < ENNReal.ofReal p ↔ 0 < p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofReal_ne_zero_iff {r : ℝ} : ENNReal.ofReal r ≠ 0 ↔ 0 < r := by
  rw [← pos_iff_ne_zero, ENNReal.ofReal_pos]

@[simp]
/-
**ENNReal.zero_eq_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：zero_eq_ofReal {p : Real} : 0 = ENNReal.ofReal p ↔ p <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `ENNReal.ofReal_eq_zero`：ofReal_eq_zero {p : Real} : ENNReal.ofReal p = 0
 ↔ p <= 0
-/
theorem zero_eq_ofReal {p : ℝ} : 0 = ENNReal.ofReal p ↔ p ≤ 0 :=
  eq_comm.trans ofReal_eq_zero

alias ⟨_, ofReal_of_nonpos⟩ := ofReal_eq_zero

@[simp]
/-
**ENNReal.ofReal_lt_natCast** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_lt_natCast {p : Real} {n : Nat} (hn : n != 0) : ENNReal.ofReal p < 
n ↔ p < n
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal_natCast`：∀ (n : ℕ), ENNReal.ofReal ↑n = ↑n
· 使用定理 `ENNReal.ofReal_lt_ofReal_iff`：ofReal_lt_ofReal_iff {p q : Real} (h : 0 <
 q) : ENNReal.ofReal p < ENNReal.ofReal q ↔ p < q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
-/
lemma ofReal_lt_natCast {p : ℝ} {n : ℕ} (hn : n ≠ 0) : ENNReal.ofReal p < n ↔ p < n := by
  exact mod_cast ofReal_lt_ofReal_iff (Nat.cast_pos.2 hn.bot_lt)

@[simp]
/-
**ENNReal.ofReal_lt_one** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_lt_one {p : Real} : ENNReal.ofReal p < 1 ↔ p < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ENNReal.ofReal_lt_natCast`：ofReal_lt_natCast {p : Real} {n : Nat} (hn : 
n != 0) : ENNReal.ofReal p < n ↔ p < n
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma ofReal_lt_one {p : ℝ} : ENNReal.ofReal p < 1 ↔ p < 1 := by
  exact mod_cast ofReal_lt_natCast one_ne_zero

@[simp]
/-
**ENNReal.ofReal_lt_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_lt_ofNat {p : Real} {n : Nat} [n.AtLeastTwo] : ENNReal.ofReal p < o
fNat(n) ↔ p < OfNat.ofNat n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.ofReal_lt_natCast`：ofReal_lt_natCast {p : Real} {n : Nat} (hn : 
n != 0) : ENNReal.ofReal p < n ↔ p < n
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Nat.AtLeastTwo.toNeZero`：∀ (n : ℕ) [n.AtLeastTwo], NeZero n
-/
lemma ofReal_lt_ofNat {p : ℝ} {n : ℕ} [n.AtLeastTwo] :
    ENNReal.ofReal p < ofNat(n) ↔ p < OfNat.ofNat n :=
  ofReal_lt_natCast (NeZero.ne n)

@[simp]
/-
**ENNReal.natCast_le_ofReal** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：natCast_le_ofReal {n : Nat} {p : Real} (hn : n != 0) : n <= ENNReal.ofReal
 p ↔ n <= p
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ENNReal.ofReal_lt_natCast`：ofReal_lt_natCast {p : Real} {n : Nat} (hn : 
n != 0) : ENNReal.ofReal p < n ↔ p < n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma natCast_le_ofReal {n : ℕ} {p : ℝ} (hn : n ≠ 0) : n ≤ ENNReal.ofReal p ↔ n ≤ p := by
  simp only [← not_lt, ofReal_lt_natCast hn]

@[simp]
/-
**ENNReal.one_le_ofReal** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：one_le_ofReal {p : Real} : 1 <= ENNReal.ofReal p ↔ 1 <= p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ENNReal.natCast_le_ofReal`：natCast_le_ofReal {n : Nat} {p : Real} (hn : 
n != 0) : n <= ENNReal.ofReal p ↔ n <= p
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma one_le_ofReal {p : ℝ} : 1 ≤ ENNReal.ofReal p ↔ 1 ≤ p := by
  exact mod_cast natCast_le_ofReal one_ne_zero

@[simp]
/-
**ENNReal.ofNat_le_ofReal** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：ofNat_le_ofReal {n : Nat} [n.AtLeastTwo] {p : Real} : ofNat(n) <= ENNReal.
ofReal p ↔ OfNat.ofNat n <= p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.natCast_le_ofReal`：natCast_le_ofReal {n : Nat} {p : Real} (hn : 
n != 0) : n <= ENNReal.ofReal p ↔ n <= p
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Nat.AtLeastTwo.toNeZero`：∀ (n : ℕ) [n.AtLeastTwo], NeZero n
-/
lemma ofNat_le_ofReal {n : ℕ} [n.AtLeastTwo] {p : ℝ} :
    ofNat(n) ≤ ENNReal.ofReal p ↔ OfNat.ofNat n ≤ p :=
  natCast_le_ofReal (NeZero.ne n)

@[simp, norm_cast]
/-
**ENNReal.ofReal_le_natCast** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_le_natCast {r : Real} {n : Nat} : ENNReal.ofReal r <= n ↔ r <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用引理 `Real.toNNReal_le_natCast`：toNNReal_le_natCast {r : Real} {n : Nat} : r.t
oNNReal <= n ↔ r <= n
-/
lemma ofReal_le_natCast {r : ℝ} {n : ℕ} : ENNReal.ofReal r ≤ n ↔ r ≤ n :=
  coe_le_coe.trans Real.toNNReal_le_natCast

@[simp]
/-
**ENNReal.ofReal_le_one** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_le_one {r : Real} : ENNReal.ofReal r <= 1 ↔ r <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用引理 `Real.toNNReal_le_one`：toNNReal_le_one {r : Real} : r.toNNReal <= 1 ↔ r <
= 1
-/
lemma ofReal_le_one {r : ℝ} : ENNReal.ofReal r ≤ 1 ↔ r ≤ 1 :=
  coe_le_coe.trans Real.toNNReal_le_one

@[simp]
/-
**ENNReal.ofReal_le_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_le_ofNat {r : Real} {n : Nat} [n.AtLeastTwo] : ENNReal.ofReal r <= 
ofNat(n) ↔ r <= OfNat.ofNat n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.ofReal_le_natCast`：ofReal_le_natCast {r : Real} {n : Nat} : ENNR
eal.ofReal r <= n ↔ r <= n
-/
lemma ofReal_le_ofNat {r : ℝ} {n : ℕ} [n.AtLeastTwo] :
    ENNReal.ofReal r ≤ ofNat(n) ↔ r ≤ OfNat.ofNat n :=
  ofReal_le_natCast

@[simp]
/-
**ENNReal.natCast_lt_ofReal** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：natCast_lt_ofReal {n : Nat} {r : Real} : n < ENNReal.ofReal r ↔ n < r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
· 使用引理 `Real.natCast_lt_toNNReal`：natCast_lt_toNNReal {r : Real} {n : Nat} : n <
 r.toNNReal ↔ n < r
-/
lemma natCast_lt_ofReal {n : ℕ} {r : ℝ} : n < ENNReal.ofReal r ↔ n < r :=
  coe_lt_coe.trans Real.natCast_lt_toNNReal

@[simp]
/-
**ENNReal.one_lt_ofReal** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：one_lt_ofReal {r : Real} : 1 < ENNReal.ofReal r ↔ 1 < r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
· 使用引理 `Real.one_lt_toNNReal`：one_lt_toNNReal {r : Real} : 1 < r.toNNReal ↔ 1 < 
r
-/
lemma one_lt_ofReal {r : ℝ} : 1 < ENNReal.ofReal r ↔ 1 < r := coe_lt_coe.trans Real.one_lt_toNNReal

@[simp]
/-
**ENNReal.ofNat_lt_ofReal** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：ofNat_lt_ofReal {n : Nat} [n.AtLeastTwo] {r : Real} : ofNat(n) < ENNReal.o
fReal r ↔ OfNat.ofNat n < r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.natCast_lt_ofReal`：natCast_lt_ofReal {n : Nat} {r : Real} : n < 
ENNReal.ofReal r ↔ n < r
-/
lemma ofNat_lt_ofReal {n : ℕ} [n.AtLeastTwo] {r : ℝ} :
    ofNat(n) < ENNReal.ofReal r ↔ OfNat.ofNat n < r :=
  natCast_lt_ofReal

@[simp]
/-
**ENNReal.ofReal_eq_natCast** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_eq_natCast {r : Real} {n : Nat} (h : n != 0) : ENNReal.ofReal r = n
 ↔ r = n
参数：h : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `ENNReal.coe_inj`：∀ {p q : NNReal}, ↑p = ↑q ↔ p = q
· 使用引理 `Real.toNNReal_eq_natCast`：toNNReal_eq_natCast {r : Real} {n : Nat} (hn :
 n != 0) : r.toNNReal = n ↔ r = n
-/
lemma ofReal_eq_natCast {r : ℝ} {n : ℕ} (h : n ≠ 0) : ENNReal.ofReal r = n ↔ r = n :=
  ENNReal.coe_inj.trans <| Real.toNNReal_eq_natCast h

@[simp]
/-
**ENNReal.ofReal_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_eq_one {r : Real} : ENNReal.ofReal r = 1 ↔ r = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `ENNReal.coe_inj`：∀ {p q : NNReal}, ↑p = ↑q ↔ p = q
· 使用引理 `Real.toNNReal_eq_one`：toNNReal_eq_one {r : Real} : r.toNNReal = 1 ↔ r = 
1
-/
lemma ofReal_eq_one {r : ℝ} : ENNReal.ofReal r = 1 ↔ r = 1 :=
  ENNReal.coe_inj.trans Real.toNNReal_eq_one

@[simp]
/-
**ENNReal.ofReal_eq_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_eq_ofNat {r : Real} {n : Nat} [n.AtLeastTwo] : ENNReal.ofReal r = o
fNat(n) ↔ r = OfNat.ofNat n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.ofReal_eq_natCast`：ofReal_eq_natCast {r : Real} {n : Nat} (h : n
 != 0) : ENNReal.ofReal r = n ↔ r = n
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Nat.AtLeastTwo.toNeZero`：∀ (n : ℕ) [n.AtLeastTwo], NeZero n
-/
lemma ofReal_eq_ofNat {r : ℝ} {n : ℕ} [n.AtLeastTwo] :
    ENNReal.ofReal r = ofNat(n) ↔ r = OfNat.ofNat n :=
  ofReal_eq_natCast (NeZero.ne n)
/-
**ENNReal.ofReal_le_iff_le_toReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_le_iff_le_toReal {a : Real} {b : Real>=0∞} (hb : b != ∞) : ENNReal.
ofReal a <= b ↔ a <= ENNReal.toReal b
参数：hb : b != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.toNNReal_le_iff_le_coe`：toNNReal_le_iff_le_coe {r : Real} {p : Real
>=0} : toNNReal r <= p ↔ r <= ↑p
-/
theorem ofReal_le_iff_le_toReal {a : ℝ} {b : ℝ≥0∞} (hb : b ≠ ∞) :
    ENNReal.ofReal a ≤ b ↔ a ≤ ENNReal.toReal b := by
  lift b to ℝ≥0 using hb
  simpa [ENNReal.ofReal, ENNReal.toReal] using Real.toNNReal_le_iff_le_coe
/-
**ENNReal.ofReal_lt_iff_lt_toReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_lt_iff_lt_toReal {a : Real} {b : Real>=0∞} (ha : 0 <= a) (hb : b !=
 ∞) : ENNReal.ofReal a < b ↔ a < ENNReal.toReal b
参数：ha : 0 <= a；hb : b != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.toNNReal_lt_iff_lt_coe`：toNNReal_lt_iff_lt_coe {r : Real} {p : Real
>=0} (ha : 0 <= r) : Real.toNNReal r < p ↔ r < ↑p
-/
theorem ofReal_lt_iff_lt_toReal {a : ℝ} {b : ℝ≥0∞} (ha : 0 ≤ a) (hb : b ≠ ∞) :
    ENNReal.ofReal a < b ↔ a < ENNReal.toReal b := by
  lift b to ℝ≥0 using hb
  simpa [ENNReal.ofReal, ENNReal.toReal] using Real.toNNReal_lt_iff_lt_coe ha
/-
**ENNReal.coe_lt_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : NNReal} {b : ℝ}, ↑a < ENNReal.ofReal b ↔ ↑a < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma coe_lt_ofReal {a : ℝ≥0} {b : ℝ} : a < ENNReal.ofReal b ↔ a < b := by
  simp [ENNReal.ofReal, Real.lt_toNNReal_iff_coe_lt]
/-
**ENNReal.ofReal_lt_coe_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_lt_coe_iff {a : Real} {b : Real>=0} (ha : 0 <= a) : ENNReal.ofReal 
a < b ↔ a < b
参数：ha : 0 <= a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `ENNReal.ofReal_lt_iff_lt_toReal`：ofReal_lt_iff_lt_toReal {a : Real} {b :
 Real>=0∞} (ha : 0 <= a) (hb : b != ∞) : ENNReal.ofReal a < b ↔ a < ENNReal.toRe
al b
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_toReal`：∀ (r : NNReal), (↑r).toReal = ↑r
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofReal_lt_coe_iff {a : ℝ} {b : ℝ≥0} (ha : 0 ≤ a) : ENNReal.ofReal a < b ↔ a < b :=
  (ofReal_lt_iff_lt_toReal ha coe_ne_top).trans <| by rw [coe_toReal]
/-
**ENNReal.le_ofReal_iff_toReal_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：le_ofReal_iff_toReal_le {a : Real>=0∞} {b : Real} (ha : a != ∞) (hb : 0 <=
 b) : a <= ENNReal.ofReal b ↔ ENNReal.toReal a <= b
参数：ha : a != ∞；hb : 0 <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.le_toNNReal_iff_coe_le`：le_toNNReal_iff_coe_le {r : Real>=0} {p : R
eal} (hp : 0 <= p) : r <= Real.toNNReal p ↔ ↑r <= p
-/
theorem le_ofReal_iff_toReal_le {a : ℝ≥0∞} {b : ℝ} (ha : a ≠ ∞) (hb : 0 ≤ b) :
    a ≤ ENNReal.ofReal b ↔ ENNReal.toReal a ≤ b := by
  lift a to ℝ≥0 using ha
  simpa [ENNReal.ofReal, ENNReal.toReal] using Real.le_toNNReal_iff_coe_le hb
/-
**ENNReal.toReal_le_of_le_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_le_of_le_ofReal {a : Real>=0∞} {b : Real} (hb : 0 <= b) (h : a <= E
NNReal.ofReal b) : ENNReal.toReal a <= b
参数：hb : 0 <= b；h : a <= ENNReal.ofReal b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `ENNReal.ofReal_ne_top`：ofReal_ne_top {r : Real} : ENNReal.ofReal r != ∞
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.le_ofReal_iff_toReal_le`：le_ofReal_iff_toReal_le {a : Real>=0∞} 
{b : Real} (ha : a != ∞) (hb : 0 <= b) : a <= ENNReal.ofReal b ↔ ENNReal.toReal 
a <= b
-/
theorem toReal_le_of_le_ofReal {a : ℝ≥0∞} {b : ℝ} (hb : 0 ≤ b) (h : a ≤ ENNReal.ofReal b) :
    ENNReal.toReal a ≤ b :=
  have ha : a ≠ ∞ := ne_top_of_le_ne_top ofReal_ne_top h
  (le_ofReal_iff_toReal_le ha hb).1 h
/-
**ENNReal.lt_ofReal_iff_toReal_lt** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：lt_ofReal_iff_toReal_lt {a : Real>=0∞} {b : Real} (ha : a != ∞) : a < ENNR
eal.ofReal b ↔ ENNReal.toReal a < b
参数：ha : a != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.lt_toNNReal_iff_coe_lt`：lt_toNNReal_iff_coe_lt {r : Real>=0} {p : R
eal} : r < Real.toNNReal p ↔ ↑r < p
-/
theorem lt_ofReal_iff_toReal_lt {a : ℝ≥0∞} {b : ℝ} (ha : a ≠ ∞) :
    a < ENNReal.ofReal b ↔ ENNReal.toReal a < b := by
  lift a to ℝ≥0 using ha
  simpa [ENNReal.ofReal, ENNReal.toReal] using Real.lt_toNNReal_iff_coe_lt
/-
**ENNReal.toReal_lt_of_lt_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_lt_of_lt_ofReal {b : Real} (h : a < ENNReal.ofReal b) : ENNReal.toR
eal a < b
参数：h : a < ENNReal.ofReal b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.lt_ofReal_iff_toReal_lt`：lt_ofReal_iff_toReal_lt {a : Real>=0∞} 
{b : Real} (ha : a != ∞) : a < ENNReal.ofReal b ↔ ENNReal.toReal a < b
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
-/
theorem toReal_lt_of_lt_ofReal {b : ℝ} (h : a < ENNReal.ofReal b) : ENNReal.toReal a < b :=
  (lt_ofReal_iff_toReal_lt h.ne_top).1 h

@[simp]
/-
**ENNReal.ofReal_mul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_mul {p q : Real} (hp : 0 <= p) : ENNReal.ofReal (p * q) = ENNReal.o
fReal p * ENNReal.ofReal q
参数：hp : 0 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.toNNReal_mul`：toNNReal_mul {p q : Real} (hp : 0 <= p) : Real.toNNRe
al (p * q) = Real.toNNReal p * Real.toNNReal q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofReal_mul {p q : ℝ} (hp : 0 ≤ p) :
    ENNReal.ofReal (p * q) = ENNReal.ofReal p * ENNReal.ofReal q := by
  simp only [ENNReal.ofReal, ← coe_mul, Real.toNNReal_mul hp]
/-
**ENNReal.ofReal_mul'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_mul' {p q : Real} (hq : 0 <= q) : ENNReal.ofReal (p * q) = ENNReal.
ofReal p * ENNReal.ofReal q
参数：hq : 0 <= q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ENNReal.ofReal_mul`：ofReal_mul {p q : Real} (hp : 0 <= p) : ENNReal.ofRe
al (p * q) = ENNReal.ofReal p * ENNReal.ofReal q
-/
theorem ofReal_mul' {p q : ℝ} (hq : 0 ≤ q) :
    ENNReal.ofReal (p * q) = ENNReal.ofReal p * ENNReal.ofReal q := by
  rw [mul_comm, ofReal_mul hq, mul_comm]

@[simp]
/-
**ENNReal.ofReal_pow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_pow {p : Real} (hp : 0 <= p) (n : Nat) : ENNReal.ofReal (p ^ n) = E
NNReal.ofReal p ^ n
参数：hp : 0 <= p；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal_eq_coe_nnreal`：ofReal_eq_coe_nnreal {x : Real} (h : 0 <= 
x) : ENNReal.ofReal x = ofNNReal (NNReal.mk x h)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_pow`：∀ (x : NNReal) (n : ℕ), ↑(x ^ n) = ↑x ^ n
· 使用定理 `ENNReal.ofReal_coe_nnreal`：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p
· 使用定理 `NNReal.coe_pow`：coe_pow (r : Real>=0) (n : Nat) : ((r ^ n : Real>=0) : R
eal) = (r : Real) ^ n
· 使用定理 `NNReal.coe_mk`：∀ (a : ℝ) (ha : 0 ≤ a), ↑(NNReal.mk a ha) = a
-/
theorem ofReal_pow {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    ENNReal.ofReal (p ^ n) = ENNReal.ofReal p ^ n := by
  rw [ofReal_eq_coe_nnreal hp, ← coe_pow, ← ofReal_coe_nnreal, NNReal.coe_pow, NNReal.coe_mk]
/-
**ENNReal.ofReal_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_nsmul {x : Real} {n : Nat} : ENNReal.ofReal (n • x) = n • ENNReal.o
fReal x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_natCast`：∀ (n : ℕ), ENNReal.ofReal ↑n = ↑n
· 使用定理 `ENNReal.ofReal_mul`：ofReal_mul {p q : Real} (hp : 0 <= p) : ENNReal.ofRe
al (p * q) = ENNReal.ofReal p * ENNReal.ofReal q
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofReal_nsmul {x : ℝ} {n : ℕ} : ENNReal.ofReal (n • x) = n • ENNReal.ofReal x := by
  simp only [nsmul_eq_mul, ← ofReal_natCast n, ← ofReal_mul n.cast_nonneg]

@[simp]
/-
**ENNReal.toNNReal_mul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toNNReal_mul {a b : Real>=0∞} : (a * b).toNNReal = a.toNNReal * b.toNNReal
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.untopD_zero_mul`：untopD_zero_mul (a b : WithTop α) : (a * b).unt
opD 0 = a.untopD 0 * b.untopD 0
-/
theorem toNNReal_mul {a b : ℝ≥0∞} : (a * b).toNNReal = a.toNNReal * b.toNNReal :=
  WithTop.untopD_zero_mul a b
/-
**ENNReal.toNNReal_mul_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toNNReal_mul_top (a : Real>=0∞) : ENNReal.toNNReal (a * ∞) = 0
参数：a : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toNNReal_mul`：toNNReal_mul {a b : Real>=0∞} : (a * b).toNNReal =
 a.toNNReal * b.toNNReal
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toNNReal_mul_top (a : ℝ≥0∞) : ENNReal.toNNReal (a * ∞) = 0 := by simp
/-
**ENNReal.toNNReal_top_mul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toNNReal_top_mul (a : Real>=0∞) : ENNReal.toNNReal (∞ * a) = 0
参数：a : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toNNReal_mul`：toNNReal_mul {a b : Real>=0∞} : (a * b).toNNReal =
 a.toNNReal * b.toNNReal
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toNNReal_top_mul (a : ℝ≥0∞) : ENNReal.toNNReal (∞ * a) = 0 := by simp

/-- `ENNReal.toNNReal` as a `MonoidHom`. -/
/-
**ENNReal.toNNRealHom** 是 Mathlib 中的一个定义，位于命名空间 `ENNReal`。
形式化陈述：toNNRealHom : Real>=0∞ ->*₀ Real>=0 where toFun
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toNNReal_zero`：ENNReal.toNNReal 0 = 0
· 使用定理 `ENNReal.toNNReal_mul`：toNNReal_mul {a b : Real>=0∞} : (a * b).toNNReal =
 a.toNNReal * b.toNNReal

--- 原说明 ---
`ENNReal.toNNReal` as a `MonoidHom`.
-/
noncomputable def toNNRealHom : ℝ≥0∞ →*₀ ℝ≥0 where
  toFun := ENNReal.toNNReal
  map_one' := toNNReal_coe _
  map_mul' _ _ := toNNReal_mul
  map_zero' := toNNReal_zero

@[simp]
/-
**ENNReal.toNNReal_pow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toNNReal_pow (a : Real>=0∞) (n : Nat) : (a ^ n).toNNReal = a.toNNReal ^ n
参数：a : Real>=0∞；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_pow`：∀ {M : Type u_4} {N : Type u_5} [inst : Monoid M] [in
st_1 : Monoid N] (f : M →* N) (a : M) (n : ℕ), f (a ^ n) = f a ^ n
-/
theorem toNNReal_pow (a : ℝ≥0∞) (n : ℕ) : (a ^ n).toNNReal = a.toNNReal ^ n :=
  toNNRealHom.map_pow a n

/-- `ENNReal.toReal` as a `MonoidHom`. -/
/-
**ENNReal.toRealHom** 是 Mathlib 中的一个定义，位于命名空间 `ENNReal`。
形式化陈述：toRealHom : Real>=0∞ ->*₀ Real
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ENNReal.toReal` as a `MonoidHom`.
-/
noncomputable def toRealHom : ℝ≥0∞ →*₀ ℝ :=
  (.ofClass NNReal.toRealHom : ℝ≥0 →*₀ ℝ).comp toNNRealHom

@[simp]
/-
**ENNReal.toReal_mul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_mul : (a * b).toReal = a.toReal * b.toReal
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZe
roOneClass α] [inst_1 : MulZeroOneClass β] (f : α →*₀ β) (a b : α),   f (a * b) 
= f a * f b
-/
theorem toReal_mul : (a * b).toReal = a.toReal * b.toReal :=
  toRealHom.map_mul a b
/-
**ENNReal.toReal_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_nsmul (a : Real>=0∞) (n : Nat) : (n • a).toReal = n • a.toReal
参数：a : Real>=0∞；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.toReal_natCast`：toReal_natCast (n : Nat) : (n : Real>=0∞).toReal
 = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toReal_nsmul (a : ℝ≥0∞) (n : ℕ) : (n • a).toReal = n • a.toReal := by simp

@[simp]
/-
**ENNReal.toReal_pow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_pow (a : Real>=0∞) (n : Nat) : (a ^ n).toReal = a.toReal ^ n
参数：a : Real>=0∞；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_pow`：∀ {M : Type u_4} {N : Type u_5} [inst : Monoid M] [in
st_1 : Monoid N] (f : M →* N) (a : M) (n : ℕ), f (a ^ n) = f a ^ n
-/
theorem toReal_pow (a : ℝ≥0∞) (n : ℕ) : (a ^ n).toReal = a.toReal ^ n :=
  toRealHom.map_pow a n
/-
**ENNReal.toReal_ofReal_mul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_ofReal_mul (c : Real) (a : Real>=0∞) (h : 0 <= c) : ENNReal.toReal 
(ENNReal.ofReal c * a) = c * ENNReal.toReal a
参数：c : Real；a : Real>=0∞；h : 0 <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
-/
theorem toReal_ofReal_mul (c : ℝ) (a : ℝ≥0∞) (h : 0 ≤ c) :
    ENNReal.toReal (ENNReal.ofReal c * a) = c * ENNReal.toReal a := by
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal h]
/-
**ENNReal.toReal_mul_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_mul_top (a : Real>=0∞) : ENNReal.toReal (a * ∞) = 0
参数：a : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `ENNReal.toReal_top`：⊤.toReal = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem toReal_mul_top (a : ℝ≥0∞) : ENNReal.toReal (a * ∞) = 0 := by
  rw [toReal_mul, toReal_top, mul_zero]
/-
**ENNReal.toReal_top_mul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_top_mul (a : Real>=0∞) : ENNReal.toReal (∞ * a) = 0
参数：a : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ENNReal.toReal_mul_top`：toReal_mul_top (a : Real>=0∞) : ENNReal.toReal (
a * ∞) = 0
-/
theorem toReal_top_mul (a : ℝ≥0∞) : ENNReal.toReal (∞ * a) = 0 := by
  rw [mul_comm]
  exact toReal_mul_top _
/-
**ENNReal.trichotomy** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (p : ENNReal), p = 0 ∨ p = ⊤ ∨ 0 < p.toReal
参数：p : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
-/
protected theorem trichotomy (p : ℝ≥0∞) : p = 0 ∨ p = ∞ ∨ 0 < p.toReal := by
  simpa only [or_iff_not_imp_left] using toReal_pos
/-
**ENNReal.trichotomy** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (p : ENNReal), p = 0 ∨ p = ⊤ ∨ 0 < p.toReal
参数：p : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
-/
protected theorem trichotomy₂ {p q : ℝ≥0∞} (hpq : p ≤ q) :
    p = 0 ∧ q = 0 ∨
      p = 0 ∧ q = ∞ ∨
        p = 0 ∧ 0 < q.toReal ∨
          p = ∞ ∧ q = ∞ ∨
            0 < p.toReal ∧ q = ∞ ∨ 0 < p.toReal ∧ 0 < q.toReal ∧ p.toReal ≤ q.toReal := by
  rcases eq_or_lt_of_le (bot_le : 0 ≤ p) with ((rfl : 0 = p) | (hp : 0 < p))
  · simpa using q.trichotomy
  rcases eq_or_lt_of_le (le_top : q ≤ ∞) with (rfl | hq)
  · simpa using p.trichotomy
  have hq' : 0 < q := lt_of_lt_of_le hp hpq
  have hp' : p < ∞ := lt_of_le_of_lt hpq hq
  simp [ENNReal.toReal_mono hq.ne hpq, ENNReal.toReal_pos_iff, hp, hp', hq', hq]
/-
**ENNReal.dichotomy** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (p : ENNReal) [Fact (1 ≤ p)], p = ⊤ ∨ 1 ≤ p.toReal
参数：p : ENNReal；1 ≤ p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `ENNReal.trichotomy₂`：∀ {p q : ENNReal},   p ≤ q →     p = 0 ∧ q = 0 ∨   
    p = 0 ∧ q = ⊤ ∨         p = 0 ∧ 0 < q.toReal ∨ p = ⊤ ∧ q = ⊤ ∨ 0 < p.toReal 
∧ q = ⊤ ∨…
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
protected theorem dichotomy (p : ℝ≥0∞) [Fact (1 ≤ p)] : p = ∞ ∨ 1 ≤ p.toReal :=
  haveI : p = ⊤ ∨ 0 < p.toReal ∧ 1 ≤ p.toReal := by
    simpa using ENNReal.trichotomy₂ (Fact.out : 1 ≤ p)
  this.imp_right fun h => h.2
/-
**ENNReal.toReal_pos_iff_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_pos_iff_ne_top (p : Real>=0∞) [Fact (1 <= p)] : 0 < p.toReal ↔ p !=
 ∞
参数：p : Real>=0∞；1 <= p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ENNReal.toReal_top`：⊤.toReal = 0
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `ENNReal.dichotomy`：∀ (p : ENNReal) [Fact (1 ≤ p)], p = ⊤ ∨ 1 ≤ p.toReal
-/
theorem toReal_pos_iff_ne_top (p : ℝ≥0∞) [Fact (1 ≤ p)] : 0 < p.toReal ↔ p ≠ ∞ :=
  ⟨fun h hp =>
    have : (0 : ℝ) ≠ 0 := toReal_top ▸ (hp ▸ h.ne : 0 ≠ ∞.toReal)
    this rfl,
    fun h => zero_lt_one.trans_le (p.dichotomy.resolve_left h)⟩

end Real

end ENNReal

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `ENNReal.ofReal`. -/
@[positivity ENNReal.ofReal _]
meta def evalENNRealOfReal : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ≥0∞), ~q(ENNReal.ofReal $a) =>
    assertInstancesCommute
    let ra ← core q(inferInstance) (some q(inferInstance)) a
    match ra with
    | .positive pa => pure (.positive q(Iff.mpr (@ENNReal.ofReal_pos $a) $pa))
    | _ => pure .none
  | _, _, _ => throwError "not ENNReal.ofReal"
end Mathlib.Meta.Positivity

